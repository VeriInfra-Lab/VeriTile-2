import VeriTile.Dist.Frontend.TritonDist.DL
import VeriTile.Dist.Frontend.TritonDist.Shmem
import VeriTile.Dist.Frontend.TritonDist.LanguageExtra
import VeriTile.Dist.State

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
  operandTypes : List ResultRegister

inductive LoopBounds where
  | counted (stop : RegName)
  | natRange (start stop step : RegName)
  | intRange (start stop step : RegName)

inductive Node where
  | code (stmts : List Stmt)
  | site (call : CallSite)
  | loop (index : RegName) (bounds : LoopBounds) (body : List Node)
  | branch (condition : RegName) (thenBody elseBody : List Node)

/-- The ports are base Triton's metadata for the rewritten quotation. They
include loads inserted for result type inference, and exclude distributed
accesses that have no base load or store. Use the statements and events to
compute footprints. -/
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
      | throwErrorAt source "dl.consume_token: expected a token bound by an earlier dl.wait in this agent"
    let some id := waits.lookup name.getId
      | throwErrorAt source "dl.consume_token: expected a token bound by an earlier dl.wait in this agent"
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
      -- A loop index shadows an enclosing wait token with the same name.
      let visible := if ["for", "tl.for", "tl.static_range"].contains
          (raw[0].getAtomVal.trimAscii.toString) && raw[1].isIdent then
        waits.filter (fun binding => binding.1 != raw[1].getId)
        else waits
      let block ← rewriteBlock nameRoot visible arg.getArgs
      args := args.set! i (arg.setArgs (block.map (·.raw)))
    else if hasDistributedSyntax arg then
      let (before, replacement) ← rewriteTree nameRoot waits arg
      prefixStmts := prefixStmts ++ before
      args := args.set! i replacement
  return (prefixStmts, raw.setArgs args)

private partial def rewriteBlock (nameRoot : String) (outer : WaitBindings)
    (stmts : Array Syntax) : RewriteM (Array TritonStmt) := do
  -- E-TD2/E-TD4 tie the access to the earlier wait in the same agent.
  -- Enclosing bindings are visible here; branch-local bindings do not escape.
  let mut waits := outer
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

private def registerDescriptor (name : RegName) (assign : Expr) : Expr :=
  let types := assign.getAppArgs
  mkApp3 (mkConst ``ResultRegister.mk) (mkStrLit name) types[0]! types[1]!

private structure SplitState where
  seen : List Nat := []
  registers : Std.HashMap RegName Expr := {}

private def makeSite (cut : Cut) (dest : Expr)
    (registers : Std.HashMap RegName Expr) : TermElabM Expr := do
  let call ← elabTerm cut.call (some (mkConst ``Call))
  let operands ← mkListLit (mkConst ``String) (cut.operands.toList.map mkStrLit)
  let types ← cut.operands.toList.mapM fun name => do
    let some ty := registers.get? name
      | throwError "TritonDist: missing operand register for site {cut.id}"
    pure ty
  let types ← mkListLit (mkConst ``ResultRegister) types
  let wait ← match cut.waitSource with
    | none => mkAppOptM ``Option.none #[some (mkConst ``Nat)]
    | some id => mkAppM ``Option.some #[mkNatLit id]
  return mkApp6 (mkConst ``CallSite.mk) (mkNatLit cut.id) call operands dest wait types

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
  let dest := registerDescriptor name stmt
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

/-- Check the identity of every cut recovered from base expansion. -/
def checkCutCoverage (expected observed : List Nat) : Except String Unit := do
  let mut seen : Std.HashSet Nat := {}
  for id in observed do
    if seen.contains id then
      throw s!"TritonDist: duplicate cut marker for site {id}"
    seen := seen.insert id
  for id in expected do
    unless seen.contains id do
      throw s!"TritonDist: missing cut marker for site {id}"

mutual

private partial def splitList (nameRoot : String) (cuts : Std.HashMap RegName Cut)
    (split : IO.Ref SplitState) (path : List Nat) (body : Expr) :
    TermElabM (Bool × Array Expr) := do
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
    let bound := assignmentName stmt
    if let some cut := bound.bind cuts.get? then
      split.modify fun s => { s with seen := cut.id :: s.seen }
      let (dest, rest) ← splitDest cut stmts
      stmts := rest
      let site ← makeSite cut dest (← split.get).registers
      nodes := (← pushCode nodes code).push (mkApp (mkConst ``Node.site) site)
      code := #[]
      hasSite := Bool.true
    else if let some (prelude, node) ← splitControl nameRoot cuts split place stmt then
      nodes := (← pushCode nodes (code ++ prelude)).push node
      code := #[]
      hasSite := Bool.true
    else
      if let some name := bound then
        split.modify fun s => { s with registers := s.registers.insert name (registerDescriptor name stmt) }
      code := code.push stmt
  return (hasSite, ← pushCode nodes code)

private partial def splitControl (nameRoot : String) (cuts : Std.HashMap RegName Cut)
    (split : IO.Ref SplitState) (path : List Nat) (stmt : Expr) :
    TermElabM (Option (Array Expr × Expr)) := do
  let args := stmt.getAppArgs
  let kind := stmt.getAppFn.constName?
  if kind == some ``Stmt.ifThen || kind == some ``Stmt.ifThenElse then
    let (hasThen, thenNodes) ← splitList nameRoot cuts split (0 :: path) args[1]!
    let (hasElse, elseNodes) ← if kind == some ``Stmt.ifThenElse then
      splitList nameRoot cuts split (1 :: path) args[2]!
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
  let (hasSite, children) ← splitList nameRoot cuts split (0 :: path) args.back!
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

private def isSimtSyntax (raw : Syntax) : Bool :=
  if !raw.isOfKind ``dlStmt then Bool.false else
  match (⟨raw[0]⟩ : TSyntax `distributedCallStmt) with
  | `(distributedCallStmt| with dl.simt_exec_region() as ($_:ident, $_:ident) { $_:tritonStmt* }) =>
    Bool.true
  | _ => Bool.false

private partial def hasCtaBarrier (raw : Syntax) : Bool :=
  if isSimtSyntax raw then Bool.false
  else if raw.isOfKind ``pendingExtraStmt then
    match (⟨raw[0]⟩ : TSyntax `extraCallStmt) with
    | `(extraCallStmt| __syncthreads()) => Bool.true
    | _ => Bool.false
  else raw.getArgs.any hasCtaBarrier

@[scoped term_elab VeriTile.Triton.DSL.tritonBlock]
def elaborateBody : TermElab := fun stx expected => do
  let `(triton { $stmts:tritonStmt* }) := stx | throwUnsupportedSyntax
  unless hasDistributedSyntax stx do throwUnsupportedSyntax
  if let some type := expected then
    let type ← whnf type
    if [``DL.Source, ``Shmem.Source, ``LanguageExtra.Source].any type.isConstOf then
      throwUnsupportedSyntax
  checkPendingCalls stx
  if (stx.find? isSimtSyntax).isSome && stmts.any (hasCtaBarrier ·.raw) then
    throwErrorAt stx "TritonDist: CTA-level __syncthreads requires a whole-CTA agent"
  let nameRoot := freshPrefix stx
  let normalized ← liftMacroM <| stmts.mapM (fun stmt => Inference.normalizeControlFlow stmt.raw)
  let (rewritten, state) ← (rewriteBlock nameRoot [] normalized).run {}
  let base ← try
    withoutErrToSorry <| elabTermAndSynthesize
      (← `(triton { $rewritten:tritonStmt* })) (some (mkConst ``ComputeKernel))
  catch e =>
    let msg ← e.toMessageData.toString
    if msg.startsWith "unexpected syntax" && (msg.splitOn nameRoot).length > 1 then
      throwErrorAt stx "unexpected syntax{indentD stx}"
    throw e
  let projected ← whnf (mkApp (mkConst ``ComputeKernel.toAlgorithm?) base)
  unless projected.getAppFn.isConstOf ``Except.ok do
    throwErrorAt stx "TritonDist: base kernel cannot project to algorithm statements{indentExpr projected}"
  let alg ← whnf projected.getAppArgs.back!
  unless alg.getAppFn.isConstOf ``Kernel.mk do
    throwErrorAt stx "TritonDist: expected an expanded algorithm kernel"
  let args := alg.getAppArgs
  let split ← IO.mkRef ({} : SplitState)
  let (_, nodes) ← splitList nameRoot state.cuts split [] args[2]!
  let expectedCuts := (state.cuts.toList.map (·.2.id)).mergeSort
  match checkCutCoverage expectedCuts (← split.get).seen.reverse with
  | .ok () => pure ()
  | .error msg => throwErrorAt stx "{msg}"
  let result := mkApp3 (mkConst ``Body.mk) args[0]! args[1]! (← nodeList nodes)
  ensureHasType expected result

end VeriTile.Dist.Frontend.TritonDist

namespace VeriTile.Dist.Frontend.TritonDist

open Lean VeriTile.Triton

/-- The launch data and the source readings used to instantiate each agent.
The byte-range resolver supplies the layout for the current block view.
Byte offsets are present only for the explicit NVSHMEM byte-view spelling. -/
structure LaunchArgs where
  agent : Agent
  numRanks : Nat
  symmetric : RegionName → Bool
  waitReading : DL.WaitReading
  order : (site n : Nat) → Equiv.Perm (Fin n)
  wholeCta : Bool
  byteRange : BlockState → Addr → Option Nat → Nat → Option (List Addr) := fun _ _ _ _ => none
  collectiveReady : Shmem.Call → Bool := fun _ => Bool.false
  teamKey : Nat := 0

/-- One event and its write payload, if the event writes a typed cell. -/
structure SiteEvent where
  event : Event
  store : Option MemCell := none

/-- A load reads one lane. The last lane commits the typed tile to the
continuation before the subsequent segment runs. -/
structure ReadLane where
  dest : ResultRegister
  lane : Nat
  last : Bool

structure SiteGroup where
  head : SiteEvent
  tail : List SiteEvent := []
  readLane : Option ReadLane := none

inductive Work where
  | code (body : List Node)
  | iterations (bindings : List Stmt) (body : List Node)
  | emit (group : SiteGroup)
  | finishWait (site : Nat)

structure Cursor where
  work : List Work
  ctaPhase : Nat := 0
  teamPhase : Nat := 0
  waits : List Nat := []
  readLanes : List (Nat × MemCell) := []
  returned : Option (ResultRegister × List (Nat × MemCell)) := none
  invalid : Bool := Bool.false

def Body.start (body : Body) : Cursor := { work := [.code body.nodes] }

/-- Execute the source program with explicit scalar and constexpr bindings.
The typed register file supplies scalar inputs, and Lean parameters of the
quotation already specialize constexprs. -/
structure Prefix where
  state : BlockState
  code : List Stmt := []

structure CutResult where
  evaluated : Prefix
  next : Option (SiteGroup × Cursor)

private def operandName (src : Syntax) : Option RegName :=
  match src[0].getId with
  | .str .anonymous name => some name
  | _ => none

private def CallSite.operandType (s : CallSite) (src : Syntax) : Option ResultRegister := do
  let name ← operandName src
  s.operandTypes.find? (·.name == name)

private def natReg (state : BlockState) (name : RegName) : Option Nat :=
  (state.regs .nat [] name).map (·.data PUnit.unit)

private def intReg (state : BlockState) (name : RegName) : Option Int :=
  (state.regs .int [] name).map (·.data PUnit.unit)

private def readOperand (state : BlockState) (reg : ResultRegister) (lane : Nat) :
    Option MemCell := do
  let tile ← state.regs reg.dtype reg.shape reg.name
  let index ← if reg.shape.isEmpty then reg.shape.allIndices.head?
    else reg.shape.allIndices[lane]?
  return MemCell.of reg.dtype (tile.data index)

private def scalarNat (v : MemCell) : Option Nat := do
  match v with
  | ⟨.nat, n⟩ => some n
  | ⟨.int, i⟩ => if i < 0 then none else some i.toNat
  | _ => none

private def pointerAddr (a : Agent) (c : MemCell) : Option Addr := do
  let (region, offset) ← c.readAs .ptr
  return ViewName.address a region offset

private def operandValue (state : BlockState) (site : CallSite) (src : Syntax) (lane : Nat) :
    Option MemCell := do
  readOperand state (← site.operandType src) lane

private def operandNat (state : BlockState) (site : CallSite) (src : Syntax) : Option Nat := do
  let reg ← site.operandType src
  guard reg.shape.isEmpty
  scalarNat (← readOperand state reg 0)

private def operandAddress (state : BlockState) (site : CallSite) (args : LaunchArgs)
    (src : Syntax) (lane : Nat) : Option Addr := do
  let addr ← pointerAddr args.agent (← operandValue state site src lane)
  guard (AccessibleAt args.symmetric args.agent addr)
  return addr

private def scalarAddress (state : BlockState) (site : CallSite) (args : LaunchArgs)
    (src : Syntax) : Option Addr := do
  guard (← site.operandType src).shape.isEmpty
  operandAddress state site args src 0

private def bytesAt (state : BlockState) (site : CallSite) (args : LaunchArgs)
    (src : Syntax) (count : Nat) : Option (List Addr) := do
  if src.isOfKind ``shmemByteView then
    match (⟨src⟩ : TSyntax `shmemPtr) with
    | `(shmemPtr| tl.cast($ptr:tritonExpr, tl.pointer_type(tl.int8))) =>
      args.byteRange state (← scalarAddress state site args ptr) (some 0) count
    | `(shmemPtr| tl.cast($ptr:tritonExpr, tl.pointer_type(tl.int8)) + $off:tritonExpr) =>
      args.byteRange state (← scalarAddress state site args ptr)
        (some (← operandNat state site off)) count
    | _ => none
  else args.byteRange state (← scalarAddress state site args src) none count

private def singleton (e : Event) : Work := .emit { head := ⟨e, none⟩ }

private def scalarResult (site : CallSite) (n : Nat) : Option Stmt := do
  let dest ← site.dest
  guard (dest.dtype = .nat ∧ dest.shape = [])
  return .assign .nat [] dest.name (.constNat n)

private def copyResult (site : CallSite) (src : Syntax) : Option Stmt := do
  let dest ← site.dest
  let reg ← site.operandType src
  guard (dest.dtype = reg.dtype ∧ dest.shape = reg.shape)
  return .assign reg.dtype reg.shape dest.name (.ref reg.dtype reg.shape reg.name)

private def pointerResult (args : LaunchArgs) (site : CallSite) (addr : Addr) : Option Stmt := do
  let dest ← site.dest
  guard (dest.dtype = .ptr ∧ dest.shape = [] ∧ AccessibleAt args.symmetric args.agent addr)
  let region := ViewName.ofSpace args.agent addr.space addr.region
  return .assign .ptr [] dest.name (.ptrAdd .nil (.ptrBase region) (.constNat addr.offset))

private def writeCode (stmt : Stmt) : Work := .code [.code [stmt]]

private def reordered (args : LaunchArgs) (site : Nat) (n : Nat) : List (Fin n) :=
  (List.finRange n).map (args.order site n)

private def lowerDL (args : LaunchArgs) (pc : Cursor) (state : BlockState)
    (site : CallSite) (call : DL.Call) : Option (Cursor × List Work) := do
  let ctx : DL.CallContext := {
    agent := args.agent, numRanks := args.numRanks, blockSize := 0
    symmetric := args.symmetric, evalAddr := scalarAddress state site args
    evalNat := operandNat state site }
  match ← call.lower ctx with
  | .scalar n => return (pc, [writeCode (← scalarResult site n)])
  | .address p => return (pc, [writeCode (← pointerResult args site p)])
  | .event e => return (pc, [singleton e])
  | .wait req =>
    let bind ← scalarResult site site.id
    let waits := (reordered args site.id req.count).map fun i =>
      singleton (req.event args.waitReading i)
    return (pc, waits ++ [.finishWait site.id, writeCode bind])
  | .afterWait src _ =>
    guard (site.waitSource.any pc.waits.contains)
    return (pc, [writeCode (← copyResult site src)])
  | .simt .. => none

private def lowerShmem (args : LaunchArgs) (pc : Cursor) (state : BlockState)
    (site : CallSite) (call : Shmem.Call) : Option (Cursor × List Work) := do
  let phase := pc.teamPhase + 1
  let ctx : Shmem.Context := {
    issuer := args.agent, peCount := args.numRanks, symmetric := args.symmetric
    evalNat := operandNat state site, evalByteRange := bytesAt state site args
    evalSignalWord := scalarAddress state site args, collectiveReady := args.collectiveReady
    teamRound := some ⟨args.teamKey, phase⟩ }
  match ← call.lower ctx with
  | .event e => return (pc, [singleton e])
  | .transfer t =>
    -- Blocking-get completion is a scheduler delivery, not an agent emission
    -- in the current S4 interface. Keep that path unprojected.
    guard (!t.completesInCall)
    return (pc, [singleton (.initiate t.transfer)])
  | .barrier b => return ({ pc with teamPhase := phase }, b.events.map singleton)

private def projectAccess (site : CallSite) (last : Bool)
    (access : LanguageExtra.AccessPlan MemCell) : Option Work :=
  match access.op with
  | .load => do
    let dest ← site.dest
    return .emit { head := ⟨.access .load access.addr access.mode, none⟩
                   readLane := some ⟨dest, access.lane, last⟩ }
  | .store value =>
    some (.emit { head := ⟨.access .store access.addr access.mode, some value⟩ })
  -- Value-form atomic promotion belongs to the S3 bridge (#696).
  | .add _ | .compareExchange .. => none

private def lowerExtra (args : LaunchArgs) (pc : Cursor) (state : BlockState)
    (site : CallSite) (call : LanguageExtra.Call) : Option (Cursor × List Work) := do
  match call with
  | .barrier =>
    let .cta c := args.agent | none
    guard args.wholeCta
    let phase := pc.ctaPhase + 1
    let plan : LanguageExtra.Barrier := ⟨c, ⟨phase, 1⟩⟩
    return ({ pc with ctaPhase := phase }, plan.events.map singleton)
  | _ =>
    let ctx : LanguageExtra.Context MemCell := {
      agent := args.agent, symmetric := args.symmetric
      laneCount := fun src => (site.operandType src).map (·.shape.allIndices.length)
      evalAddr := operandAddress state site args, evalValue := operandValue state site
      evalMask := fun src => do
        let r ← site.operandType src
        let t ← state.regs .bool r.shape r.name
        return r.shape.allIndices.map t.data
      evalWordValue := operandNat state site, threadCoord := fun _ => none }
    match ← call.lower ctx with
    | .scalar n => return (pc, [writeCode (← scalarResult site n)])
    | .unspecified | .barrier _ => none
    | .step [] => return (pc, [])
    | .step (e :: es) =>
      return (pc, [.emit { head := ⟨e, none⟩, tail := es.map (⟨·, none⟩) }])
    | .accesses accesses =>
      let array := accesses.toArray
      let order := reordered args site.id array.size
      let work ← order.zipIdx.mapM fun (i, pos) =>
        projectAccess site (pos + 1 == array.size) array[i]
      return (pc, work)

private def lowerSite (args : LaunchArgs) (pc : Cursor) (state : BlockState)
    (site : CallSite) : Option (Cursor × List Work) :=
  match site.call with
  | .dl call => lowerDL args pc state site call
  | .shmem call => lowerShmem args pc state site call
  | .extra call => lowerExtra args pc state site call

mutual
private def noAtomicStmt : Stmt → Bool
  | .atomicAdd .. | .atomicRMW .. => Bool.false
  | .forLoop _ _ body | .forRange _ _ _ _ body | .forRangeDyn _ _ _ _ body
  | .forRangeInt _ _ _ _ body | .ifThen _ body => noAtomicStmts body
  | .ifThenElse _ yes no => noAtomicStmts yes && noAtomicStmts no
  | .assign .. | .store .. => Bool.true

def noAtomicStmts : List Stmt → Bool
  | [] => Bool.true
  | stmt :: rest => noAtomicStmt stmt && noAtomicStmts rest
end

-- Expose the common nonrecursive cases to kernel reduction without
-- unfolding the upstream well-founded fixed point at each assignment.
private noncomputable def stepPrefixStmt : Stmt → BlockState → Option BlockState
  | .assign dtype shape name op, state => do
    let value ← evalOp op state
    return state.setReg name dtype shape value
  | .store dtype [] (.region region offset) op .none, state => do
    let value ← evalOp op state
    let offset ← evalOp offset state
    return state.writeMemTyped dtype (Region.cast region) (offset.data PUnit.unit)
      (value.data PUnit.unit)
  | .store dtype [] (.ptr ptr) op .none, state => do
    let value ← evalOp op state
    let address := (← evalOp ptr state).data PUnit.unit
    return state.writeMemTyped dtype address.1 address.2 (value.data PUnit.unit)
  | stmt, state => stepStmt stmt state

private theorem stepPrefixStmt_eq (stmt : Stmt) (state : BlockState) :
    stepPrefixStmt stmt state = stepStmt stmt state := by
  unfold stepPrefixStmt
  split <;> first | rfl | (rw [stepStmt]; rfl)

private noncomputable def stepPrefixCode : List Stmt → BlockState → Option BlockState
  | [], state => some state
  | stmt :: rest, state => do
    stepPrefixCode rest (← stepPrefixStmt stmt state)

theorem stepPrefixCode_eq (code : List Stmt) (state : BlockState) :
    stepPrefixCode code state = stepStmts code state := by
  induction code generalizing state with
  | nil => simp [stepPrefixCode]
  | cons stmt rest ih =>
    rw [stepPrefixCode, stepStmts, stepPrefixStmt_eq]
    cases h : stepStmt stmt state with
    | none => rfl
    | some after => exact ih after

#print axioms stepPrefixStmt_eq
#print axioms stepPrefixCode_eq

private noncomputable def Prefix.run (evaluated : Prefix) (code : List Stmt) : Option Prefix := do
  guard (noAtomicStmts code)
  return ⟨← stepPrefixCode code evaluated.state, evaluated.code ++ code⟩

private def iterationBindings (state : BlockState) (index : RegName) :
    LoopBounds → Option (List Stmt)
  | .counted stop => do
    return (List.range (← natReg state stop)).map fun i => .assign .nat [] index (.constNat i)
  | .natRange start stop stride => do
    let first ← natReg state start
    let last ← natReg state stop
    let step ← natReg state stride
    let count := if step = 0 then 0 else (last - first + step - 1) / step
    return (List.range count).map fun i => .assign .nat [] index (.constNat (first + i * step))
  | .intRange start stop stride => do
    let first ← intReg state start
    let last ← intReg state stop
    let step ← natReg state stride
    let count := if step = 0 then 0 else ((last - first).toNat + step - 1) / step
    return (List.range count).map fun i => .assign .int [] index (.constInt (first + i * step))

private inductive Advance where
  | more (evaluated : Prefix) (pc : Cursor)
  | cut (evaluated : Prefix) (event : SiteGroup) (pc : Cursor)

private noncomputable def visitSite (evaluated : Prefix) (pc : Cursor) : List Work → Option Advance
  | [] => some (.more evaluated pc)
  | .code [.code code] :: more => do
    visitSite (← evaluated.run code) pc more
  | .finishWait id :: more => visitSite evaluated { pc with waits := id :: pc.waits } more
  | .emit e :: more => some (.cut evaluated e { pc with work := more })
  | _ => none

private noncomputable def visitIterations
    (visit : Prefix → Cursor → Option Advance) (body : List Node) :
    List Stmt → Prefix → Cursor → Option Advance
  | [], evaluated, pc => some (.more evaluated pc)
  | binding :: rest, evaluated, pc => do
    match ← visit (← evaluated.run [binding]) pc with
    | .more p k => visitIterations visit body rest p k
    | .cut p evt k => return (.cut p evt { k with work := k.work ++ [.iterations rest body] })

mutual
private noncomputable def visitNodes (args : LaunchArgs) :
    (body : List Node) → Prefix → Cursor → Option Advance
  | [], evaluated, pc => some (.more evaluated pc)
  | node :: rest, evaluated, pc => do
    match ← visitNode args node evaluated pc with
    | .more p k => visitNodes args rest p k
    | .cut p evt k => return (.cut p evt { k with work := k.work ++ [.code rest] })
termination_by structural body _ _ => body

private noncomputable def visitNode (args : LaunchArgs) :
    (node : Node) → Prefix → Cursor → Option Advance
  | .code code, evaluated, pc => do
    return .more (← evaluated.run code) pc
  | .site site, evaluated, pc => do
    let (next, work) ← lowerSite args pc evaluated.state site
    visitSite evaluated next work
  | .branch condition yes no, evaluated, pc => do
    let v ← evaluated.state.regs .bool [] condition
    if v.data PUnit.unit then visitNodes args yes evaluated pc else visitNodes args no evaluated pc
  | .loop idx bounds body, evaluated, pc => do
    let indices ← iterationBindings evaluated.state idx bounds
    visitIterations (visitNodes args body) body indices evaluated pc
termination_by structural node _ _ => node
end

private noncomputable def visitWork (args : LaunchArgs) :
    List Work → Prefix → Cursor → Option CutResult
  | [], evaluated, _ => some ⟨evaluated, none⟩
  | task :: rest, evaluated, pc => do
    let advanced ← match task with
      | .code body => visitNodes args body evaluated pc
      | .iterations bindings body => visitIterations (visitNodes args body) body bindings evaluated pc
      | .emit group => return ⟨evaluated, some (group, { pc with work := rest })⟩
      | .finishWait site => return ← visitWork args rest evaluated { pc with waits := site :: pc.waits }
    match advanced with
    | .more p k => visitWork args rest p k
    | .cut p evt k => return ⟨p, some (evt, { k with work := k.work ++ rest })⟩

/-- Apply a completed memory-read continuation to the next segment's
register file. Each lane must exist and have the declared dtype. -/
noncomputable def Cursor.enter (pc : Cursor) (state : BlockState) : Option BlockState := do
  guard (!pc.invalid)
  let some (reg, lanes) := pc.returned | return state
  let values ← (List.range reg.shape.product).mapM fun lane => do
    let cell ← lanes.lookup lane
    cell.readAs reg.dtype
  let tile : Tile reg.dtype reg.shape := ⟨fun index =>
    values[reg.shape.linearIndex index]?.getD (BlockState.defaultCarrier reg.dtype)⟩
  return state.setReg reg.name reg.dtype reg.shape tile

def Cursor.resume (pc : Cursor) (event : SiteGroup) (results : List (Option MemCell)) : Cursor :=
  match event.readLane with
  | none => pc
  | some r =>
    match results with
    | [some value] =>
      let lanes := (r.lane, value) :: pc.readLanes
      if r.last then { pc with readLanes := [], returned := some (r.dest, lanes) }
      else { pc with readLanes := lanes }
    | _ => { pc with invalid := Bool.true }

/-- Evaluate the maximal sequential prefix, stopping before the next event.
Failure means the input, control path or source operation has no projection. -/
noncomputable def Cursor.prepare (pc : Cursor) (args : LaunchArgs)
    (state : BlockState) : Option CutResult := do
  guard (args.agent.cta?.isSome && args.agent.rankOf < args.numRanks)
  let state ← pc.enter state
  visitWork args pc.work ⟨state, []⟩ { pc with work := [], returned := none }

end VeriTile.Dist.Frontend.TritonDist
