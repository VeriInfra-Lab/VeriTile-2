import VeriTile.Dist.Frontend.TritonDist.DL
import VeriTile.Dist.Frontend.TritonDist.Shmem
import VeriTile.Dist.Frontend.TritonDist.LanguageExtra

/-! Compose the signed call frontends with the base Triton algorithm IR.
The resulting body retains control flow and the inputs and continuations of
distributed calls. Instantiation and event projection consume this IR. -/

namespace VeriTile.Dist.Frontend.TritonDist

open Lean Meta Elab Term
open VeriTile.Triton VeriTile.Triton.DSL
open scoped VeriTile.Dist.Frontend.TritonDist

inductive Call where
  | dl (call : DL.Call)
  | shmem (call : Shmem.Call)
  | extra (call : LanguageExtra.Call)

structure ResultRegister where
  name : RegName
  dtype : TileDType
  shape : TileShape

structure CallSite where
  id : Nat
  call : Call
  operands : List RegName
  dest : Option ResultRegister
  /-- The earlier wait site whose token this call consumes. -/
  waitSource : Option Nat

inductive LoopBounds where
  | counted (stop : RegName)
  | natRange (start stop step : RegName)
  | intRange (start stop step : RegName)

inductive Node where
  | code (stmts : List Stmt)
  | site (call : CallSite)
  | loop (index : RegName) (bounds : LoopBounds) (body : List Node)
  | branch (condition : RegName) (thenBody elseBody : List Node)

structure Body where
  inputs : List RegionName
  outputs : List RegionName
  nodes : List Node

private abbrev TritonStmt := TSyntax `tritonStmt
private abbrev TritonExpr := TSyntax `tritonExpr
private abbrev WaitBindings := List (Name × Nat)

private structure Cut where
  id : Nat
  call : TSyntax `term
  operands : Array RegName
  dest : Option RegName
  waitSource : Option Nat

private structure RewriteState where
  cuts : Std.HashMap RegName Cut := {}
  nextId : Nat := 0

private abbrev RewriteM := StateRefT RewriteState TermElabM

private def assignedNames (stx : Syntax) : List Name :=
  let lhs := stx.getArgs.toList.takeWhile fun arg =>
    !(arg.isAtom && ["=", ":=", "+=", "-=", "*=", "/="].contains arg.getAtomVal)
  if lhs.length == stx.getNumArgs then [] else
    lhs.filterMap fun arg => if arg.isIdent then some arg.getId else none

private partial def writes (stx : Syntax) : List Name :=
  assignedNames stx ++ stx.getArgs.toList.flatMap writes

private partial def unparen (e : TritonExpr) : TritonExpr :=
  match e with
  | `(tritonExpr| ($inner:tritonExpr)) => unparen inner
  | _ => e

private def isWaitAssignment (stx : Syntax) : Bool :=
  match (⟨stx⟩ : TritonStmt) with
  | `(tritonStmt| $_:ident = $rhs:tritonExpr)
  | `(tritonStmt| $_:ident := $rhs:tritonExpr) =>
    let raw := (unparen rhs).raw
    if !raw.isOfKind ``dlExpr then Bool.false else
    match (⟨raw[0]⟩ : TSyntax `distributedCallExpr) with
    | `(distributedCallExpr| dl.wait($_:tritonExpr, $_:tritonExpr, $_:tritonExpr, $_:tritonExpr))
    | `(distributedCallExpr| dl.wait($_:tritonExpr, $_:tritonExpr, $_:tritonExpr, $_:tritonExpr, waitValue=$_:tritonExpr))
    | `(distributedCallExpr| dl.wait($_:tritonExpr, $_:tritonExpr, scope=$_:tritonExpr, semantic=$_:tritonExpr, waitValue=$_:tritonExpr)) => Bool.true
    | _ => Bool.false
  | _ => Bool.false

private def hasDistributedSyntax (stx : Syntax) : Bool :=
  (stx.find? (fun s => (family? s.getKind).isSome)).isSome

private def startsWithName (nameRoot : String) (stx : Syntax) : Bool :=
  (stx.find? fun s => s.isIdent && s.getId.toString.startsWith nameRoot).isSome

/-- The source and split passes share a namespace absent from the input. -/
private def freshPrefix (stx : Syntax) : String := Id.run do
  let mut nameRoot := "__triton_dist_"
  while startsWithName nameRoot stx do
    nameRoot := nameRoot ++ "_"
  return nameRoot

private structure CapturedOperand where
  name : Ident
  kind : OperandKind
  input : TritonExpr

/-- A key passed to the existing Call.lower interface. The continuation
reads the corresponding register after executing the preceding code. -/
private def captureOperand (nameRoot : String) (waits : WaitBindings)
    (saved : IO.Ref (Array CapturedOperand)) (waitSource : IO.Ref (Option Nat)) :
    QuoteOperand := fun kind source => do
  if kind == .token then
    let `(tritonExpr| $name:ident) := unparen ⟨source⟩
      | throwErrorAt source "dl.consume_token: expected a token bound by an earlier dl.wait in this block"
    let some id := waits.lookup name.getId
      | throwErrorAt source "dl.consume_token: expected a token bound by an earlier dl.wait in this block"
    waitSource.set (some id)
    return ← quoteDistSyntax (← `(tritonExpr| $name:ident))
  let save (kind : OperandKind) (input : TritonExpr) : TermElabM Ident := do
    let index := (← saved.get).size
    let name := mkIdentFrom source (Name.mkSimple (nameRoot ++ "arg" ++ toString index))
    saved.modify (·.push ⟨name, kind, input⟩)
    pure name
  if source.isOfKind ``shmemByteView then
    -- Keep the explicit byte view, including its optional byte offset.
    let ptr ← save .address ⟨source[1]⟩
    let ptr ← `(tritonExpr| $ptr:ident)
    let view ← match (⟨source⟩ : TSyntax `shmemPtr) with
      | `(shmemPtr| tl.cast($_:tritonExpr, tl.pointer_type(tl.int8))) =>
        `(shmemPtr| tl.cast($ptr:tritonExpr, tl.pointer_type(tl.int8)))
      | `(shmemPtr| tl.cast($_:tritonExpr, tl.pointer_type(tl.int8)) + $off:tritonExpr) => do
        let offset ← save .nat off
        let off ← `(tritonExpr| $offset:ident)
        `(shmemPtr| tl.cast($ptr:tritonExpr, tl.pointer_type(tl.int8)) + $off:tritonExpr)
      | _ => throwErrorAt source "unsupported NVSHMEM byte view"
    return ← quoteDistSyntax view
  let name ← save kind ⟨source⟩
  quoteDistSyntax (← `(tritonExpr| $name:ident))

private def natLiteral (n : TSyntax `num) : TermElabM TritonExpr := do
  let term ← `(($n : Nat))
  `(tritonExpr| $($term))

private def operandExpr (kind : OperandKind) (input : TritonExpr) : TermElabM TritonExpr := do
  match unparen input with
  | `(tritonExpr| $_:ident) => do
    if kind == .address then
      let zero ← natLiteral ⟨Syntax.mkNumLit "0"⟩
      `(tritonExpr| $input + $zero:tritonExpr)
    else pure input
  | `(tritonExpr| $n:num) =>
    if kind == .nat then natLiteral n else pure input
  | _ => pure input

/-- The placeholder establishes the result's register type through base
elaboration. The split checks and removes it before emitting the body. -/
private def placeholder (raw : Syntax) (operands : Array CapturedOperand) :
    TermElabM TritonExpr := do
  let registerAt (index : Nat) : TermElabM Ident := do
    let some operand := operands[index]? | throwErrorAt raw "missing distributed result operand"
    pure operand.name
  if raw.isOfKind ``dlExpr then
    match (⟨raw[0]⟩ : TSyntax `distributedCallExpr) with
    | `(distributedCallExpr| dl.symm_at($_:tritonExpr, $_:tritonExpr))
    | `(distributedCallExpr| dl.consume_token($_:tritonExpr, $_:tritonExpr)) =>
      let input ← registerAt 0
      return ← `(tritonExpr| $input:ident)
    | _ => pure ()
  if raw.isOfKind ``pendingExtraExpr then
    match (⟨raw[0]⟩ : TSyntax `extraCallExpr) with
    | `(extraCallExpr| __shfl_sync_i32($_:tritonExpr, $_:tritonExpr, $_:tritonExpr))
    | `(extraCallExpr| __shfl_up_sync_i32($_:tritonExpr, $_:tritonExpr, $_:tritonExpr)) =>
      let input ← registerAt 1
      return ← `(tritonExpr| $input:ident)
    | _ =>
      if let some ptr := operands.find? (·.kind == .address) then
        let source ← `(tritonExpr| $ptr.name:ident)
        return ← `(tritonExpr| tl.load($source:tritonExpr))
  natLiteral ⟨Syntax.mkNumLit "0"⟩

private def quoteComposedCall (raw : Syntax) (operand : QuoteOperand) :
    TermElabM (TSyntax `term) := do
  if let some call ← DL.quoteCall raw operand then
    if let `(distributedCallStmt| with dl.simt_exec_region() as ($_:ident, $_:ident) { $_:tritonStmt* }) :=
        (⟨raw[0]⟩ : TSyntax `distributedCallStmt) then
      throwErrorAt raw "dl.simt_exec_region: composed elaboration requires thread-program support"
    return ← `(Call.dl $call)
  if raw.isOfKind ``pendingShmemStmt then
    let call ← Shmem.quoteCall operand ⟨raw[0]⟩
    return ← `(Call.shmem $call)
  let call ←
    if raw.isOfKind ``pendingExtraExpr then LanguageExtra.quoteExpr operand ⟨raw[0]⟩
    else if raw.isOfKind ``pendingExtraStmt then LanguageExtra.quoteStmt operand ⟨raw[0]⟩
    else if (raw[1].find? (·.isOfKind ``pendingExtraExpr)).isSome then
      LanguageExtra.quoteSpin operand ⟨raw[1]⟩
    else
      throwErrorAt raw "TritonDist: empty while requires a language_extra polling call"
  `(Call.extra $call)

mutual

private partial def rewriteTree (nameRoot : String) (waits : WaitBindings) (raw : Syntax) :
    RewriteM (Array TritonStmt × Syntax) := do
  if (family? raw.getKind).isSome then
    return ← rewriteCall nameRoot waits raw
  let mut prefixStmts := #[]
  let mut args := raw.getArgs
  for i in [:args.size] do
    let arg := args[i]!
    let previous := if i == 0 then Syntax.missing else args[i - 1]!
    if arg.isOfKind nullKind && previous.getAtomVal == "{" then
      let block ← rewriteBlock nameRoot arg.getArgs
      args := args.set! i (arg.setArgs (block.map (·.raw)))
    else if hasDistributedSyntax arg then
      let (before, replacement) ← rewriteTree nameRoot waits arg
      prefixStmts := prefixStmts ++ before
      args := args.set! i replacement
  return (prefixStmts, raw.setArgs args)

private partial def rewriteBlock (nameRoot : String) (stmts : Array Syntax) :
    RewriteM (Array TritonStmt) := do
  let mut waits : WaitBindings := []
  let mut result := #[]
  for stmt in stmts do
    let id := (← get).nextId
    let (before, rewritten) ← rewriteTree nameRoot waits stmt
    result := result ++ before
    unless rewritten.isMissing do result := result.push ⟨rewritten⟩
    let rebound := writes stmt
    waits := waits.filter (fun entry => !rebound.contains entry.1)
    if isWaitAssignment stmt then
      if let [dest] := assignedNames stmt then
        waits := (dest, id) :: waits
  return result

private partial def rewriteCall (nameRoot : String) (waits : WaitBindings) (raw : Syntax) :
    RewriteM (Array TritonStmt × Syntax) := do
  let id := (← get).nextId
  modify fun s => { s with nextId := id + 1 }
  let stem := nameRoot ++ "site" ++ toString id ++ "_"
  let saved ← IO.mkRef #[]
  let waitSource ← IO.mkRef none
  let call ← liftM <| quoteComposedCall raw (captureOperand stem waits saved waitSource)
  let operands ← saved.get
  let mut stmts := #[]
  for arg in operands do
    let (earlier, input) ← rewriteTree nameRoot waits arg.input.raw
    let value ← liftM <| operandExpr arg.kind ⟨input⟩
    let reg := arg.name
    let assign ← liftMacroM <| `(tritonStmt| $reg:ident = $value:tritonExpr)
    stmts := stmts ++ earlier |>.push assign
  let marker := mkIdentFrom raw (Name.mkSimple (stem ++ "cut"))
  let cut ← liftMacroM <| `(tritonStmt| $marker:ident = 0)
  stmts := stmts.push cut
  let mut replacement := Syntax.missing
  let mut dest := none
  if raw.isOfKind ``dlExpr || raw.isOfKind ``pendingExtraExpr then
    let reg := mkIdentFrom raw (Name.mkSimple (stem ++ "result"))
    let value ← liftM <| placeholder raw operands
    let assign ← liftMacroM <| `(tritonStmt| $reg:ident = $value:tritonExpr)
    stmts := stmts.push assign
    replacement := (← liftMacroM <| `(tritonExpr| $reg:ident)).raw
    dest := some reg.getId.toString
  let entry := ⟨id, call, operands.map (·.name.getId.toString), dest, ← waitSource.get⟩
  modify fun s => { s with cuts := s.cuts.insert marker.getId.toString entry }
  return (stmts, replacement)

end

private def assignmentName (stmt : Expr) : Option String :=
  if stmt.getAppFn.isConstOf ``Stmt.assign then
    getStringValue? stmt.getAppArgs[2]!
  else none

private def makeSite (cut : Cut) (dest : Expr) : TermElabM Expr := do
  let call ← elabTerm cut.call (some (mkConst ``Call))
  let operands ← mkListLit (mkConst ``String) (cut.operands.toList.map mkStrLit)
  let wait ← match cut.waitSource with
    | none => mkAppOptM ``Option.none #[some (mkConst ``Nat)]
    | some id => mkAppM ``Option.some #[mkNatLit id]
  return mkApp5 (mkConst ``CallSite.mk) (mkNatLit cut.id) call operands dest wait

private def splitDest (cut : Cut) (stmts : Expr) : TermElabM (Expr × Expr) := do
  let some name := cut.dest
    | return (← mkAppOptM ``Option.none #[some (mkConst ``ResultRegister)], stmts)
  let list ← whnf stmts
  unless list.getAppFn.isConstOf ``List.cons do
    throwError "TritonDist: missing result register for site {cut.id}"
  let args := list.getAppArgs
  let stmt ← whnf args[1]!
  unless assignmentName stmt == some name do
    throwError "TritonDist: misplaced result register for site {cut.id}"
  let types := stmt.getAppArgs
  let dest := mkApp3 (mkConst ``ResultRegister.mk) (mkStrLit name) types[0]! types[1]!
  return (← mkAppM ``Option.some #[dest], args[2]!)

private def mkAssign (dtype : Name) (name : Expr) (value : Expr) : Expr :=
  mkApp4 (mkConst ``Stmt.assign) (mkConst dtype)
    (mkApp (mkConst ``List.nil [Level.zero]) (mkConst ``Nat)) name value

private def nodeList (nodes : Array Expr) : MetaM Expr :=
  mkListLit (mkConst ``Node) nodes.toList

private def pushCode (nodes code : Array Expr) : MetaM (Array Expr) := do
  if code.isEmpty then return nodes
  let stmts ← mkListLit (mkConst ``Stmt) code.toList
  return nodes.push (mkApp (mkConst ``Node.code) stmts)

private def controlRegister (nameRoot : String) (path : List Nat) (role : String) : Expr :=
  mkStrLit (nameRoot ++ "control_" ++ String.intercalate "_" (path.reverse.map toString) ++ "_" ++ role)

mutual

private partial def splitList (nameRoot : String) (cuts : Std.HashMap RegName Cut)
    (path : List Nat) (body : Expr) : TermElabM (Bool × Array Expr) := do
  let mut nodes := #[]
  let mut code := #[]
  let mut stmts := body
  let mut hasSite := Bool.false
  let mut index := 0
  repeat
    let list ← whnf stmts
    if list.getAppFn.isConstOf ``List.nil then break
    unless list.getAppFn.isConstOf ``List.cons do
      throwError "TritonDist: expected a finite base statement list"
    let args := list.getAppArgs
    let stmt ← whnf args[1]!
    stmts := args[2]!
    let place := index :: path
    index := index + 1
    if let some cut := (assignmentName stmt).bind cuts.get? then
      let (dest, rest) ← splitDest cut stmts
      stmts := rest
      let site ← makeSite cut dest
      nodes := (← pushCode nodes code).push (mkApp (mkConst ``Node.site) site)
      code := #[]
      hasSite := Bool.true
    else if let some (prelude, node) ← splitControl nameRoot cuts place stmt then
      nodes := (← pushCode nodes (code ++ prelude)).push node
      code := #[]
      hasSite := Bool.true
    else
      code := code.push stmt
  return (hasSite, ← pushCode nodes code)

private partial def splitControl (nameRoot : String) (cuts : Std.HashMap RegName Cut)
    (path : List Nat) (stmt : Expr) : TermElabM (Option (Array Expr × Expr)) := do
  let args := stmt.getAppArgs
  let kind := stmt.getAppFn.constName?
  if kind == some ``Stmt.ifThen || kind == some ``Stmt.ifThenElse then
    let (hasThen, thenNodes) ← splitList nameRoot cuts (0 :: path) args[1]!
    let (hasElse, elseNodes) ← if kind == some ``Stmt.ifThenElse then
      splitList nameRoot cuts (1 :: path) args[2]!
      else pure (Bool.false, #[])
    unless hasThen || hasElse do return none
    let condition := controlRegister nameRoot path "condition"
    let prelude := #[mkAssign ``TileDType.bool condition args[0]!]
    let node := mkApp3 (mkConst ``Node.branch) condition
      (← nodeList thenNodes) (← nodeList elseNodes)
    return some (prelude, node)
  let isCounted := kind == some ``Stmt.forLoop
  let isStatic := kind == some ``Stmt.forRange
  let isSigned := kind == some ``Stmt.forRangeInt
  unless isCounted || isStatic || isSigned || kind == some ``Stmt.forRangeDyn do return none
  let (hasSite, children) ← splitList nameRoot cuts (0 :: path) args.back!
  unless hasSite do return none
  let children ← nodeList children
  let index := args[0]!
  let liftNat := fun n => mkApp (mkConst ``Op.constNat) n
  let stop := controlRegister nameRoot path "stop"
  if isCounted then
    let prelude := #[mkAssign ``TileDType.nat stop (liftNat args[1]!)]
    let bounds := mkApp (mkConst ``LoopBounds.counted) stop
    return some (prelude, mkApp3 (mkConst ``Node.loop) index bounds children)
  let start := controlRegister nameRoot path "start"
  let step := controlRegister nameRoot path "step"
  let value := fun i => if isStatic then liftNat args[i]! else args[i]!
  let dtype := if isSigned then ``TileDType.int else ``TileDType.nat
  let prelude := #[mkAssign dtype start (value 1), mkAssign dtype stop (value 2),
    mkAssign ``TileDType.nat step (value 3)]
  let bounds := mkApp3 (mkConst (if isSigned then ``LoopBounds.intRange else ``LoopBounds.natRange))
    start stop step
  return some (prelude, mkApp3 (mkConst ``Node.loop) index bounds children)

end

@[scoped term_elab VeriTile.Triton.DSL.tritonBlock]
def elaborateBody : TermElab := fun stx expected => do
  let `(triton { $stmts:tritonStmt* }) := stx | throwUnsupportedSyntax
  unless hasDistributedSyntax stx do throwUnsupportedSyntax
  if let some type := expected then
    let type ← whnf type
    if [``DL.Source, ``Shmem.Source, ``LanguageExtra.Source].any type.isConstOf then
      throwUnsupportedSyntax
  checkPendingCalls stx
  let nameRoot := freshPrefix stx
  let normalized ← liftMacroM <| stmts.mapM (fun stmt => Inference.normalizeControlFlow stmt.raw)
  let (rewritten, state) ← (rewriteBlock nameRoot normalized).run {}
  let base ← withoutErrToSorry <| elabTermAndSynthesize
    (← `(triton { $rewritten:tritonStmt* })) (some (mkConst ``ComputeKernel))
  let projected ← whnf (mkApp (mkConst ``ComputeKernel.toAlgorithm?) base)
  unless projected.getAppFn.isConstOf ``Except.ok do
    throwErrorAt stx "TritonDist: base kernel cannot project to algorithm statements{indentExpr projected}"
  let alg ← whnf projected.getAppArgs.back!
  unless alg.getAppFn.isConstOf ``Kernel.mk do
    throwErrorAt stx "TritonDist: expected an expanded algorithm kernel"
  let args := alg.getAppArgs
  let (_, nodes) ← splitList nameRoot state.cuts [] args[2]!
  let result := mkApp3 (mkConst ``Body.mk) args[0]! args[1]! (← nodeList nodes)
  ensureHasType expected result

end VeriTile.Dist.Frontend.TritonDist
