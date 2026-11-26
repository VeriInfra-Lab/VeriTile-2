import VeriTile.Triton.DSL.SourceProcedures
import VeriTile.Triton.DSL.PythonFullConstructors

/-!
Finite constexpr specialization for the retained Triton-distributed sources,
pinned at 7908e4ea9010bb2238f9f05b28c904fd4b71c60a:

* The pointer element-width form `tl.constexpr(ptr.dtype.element_ty.primitive_bitwidth)`
  occurs as a dividend in `all_to_all_vdev_2d_offset.py:279,414`,
  `all_to_all_vdev_2d_offset_inter_node.py:118–119`, `allreduce.py:349,409,463,544`,
  `reduce_scatter.py:484` (kernel paths under `python/triton_dist/kernels/nvidia/`),
  and `tutorials/06-inter-node-reduce-scatter.py:255`. It occurs as the divisor
  of 128 in `allreduce.py:642,669`.
* `common_ops.py:83,102–103,132` uses `tl.constexpr` as the identity on already
  static inputs. The three call productions are scoped and use existing tokens.
* all_to_all_single_2d.py:37 asks for `len(tensor.shape)`. Supply a Lean
  `let «tensor.shape» : List Nat := …` in scope of the quotation. This is a
  trusted transcription binding. The frontend reads only its length and
  does not check that it matches the source tensor. Extents may be symbolic.
  See Python 3.11's `len` documentation (accessed 2026-11-22):
  https://docs.python.org/3.11/library/functions.html#len
* allgather_group_gemm.py:74,100–101 imports `next_power_of_2` from
  common_ops.py:270–272. Opening this extension gives that exact unqualified
  call its pinned import meaning. Triton v3.5.1 documents the least power of two
  ≥ n (accessed 2026-11-24):
  https://github.com/triton-lang/triton/blob/v3.5.1/python/triton/__init__.py#L72-L82
  The specialization accepts zero and positive integers through 2^64, the
  coverage of the pinned shifts for positive inputs. The pinned code gives
  zero for zero and, for example, for −1. The adapter rejects negative inputs.
  Qualified `triton.next_power_of_2` calls in Python launch and sizing code
  run on the host: `all_to_all_single_2d.py:186`,
  `all_to_all_vdev_2d_offset_inter_node.py:438`, `allgather_group_gemm.py:182,227`,
  `allreduce.py:931`, `moe_reduce_ar.py:213,680–681`, and
  `moe_reduce_rs.py:817,952,954`.

`reduce_scatter.py:404` queries the pointer dtype directly, without `element_ty`.
The pointer dtype has no such primitive-width property and the helper has no
retained production caller. The adapter rejects this spelling.
`tutorials/04-deepseek-infer-all2all.py:82–83` uses torch-derived and floating
constants at module scope. Its reference quantization kernel at line 344
uses `FP8_MAX_INV = tl.constexpr(1 / 448.)`. Supply such constants through
the existing explicit transcription bindings.

For a bare block, scalar names can be bound by enclosing Lean lets and
pointer dtypes by `tl.region`. Pasted call bodies use signature constexpr
names, source constants and fixed pointer types. Runtime arguments are never
compile-time bindings. The adapter evaluates only Lean data and leaves
unrelated expressions and source instructions to the existing frontend.
An integer folded into a register assignment is materialized with its
Triton integer dtype. In Triton v3.5.1, `visit_Assign` unwraps the constexpr
and calls `to_tensor`, which selects the dtype by the integer's range
(accessed 2026-11-25).
https://github.com/triton-lang/triton/blob/v3.5.1/python/triton/compiler/code_generator.py#L678-L699
https://github.com/triton-lang/triton/blob/v3.5.1/python/triton/language/semantic.py#L117-L132
Static dimensions and inline operands retain literal syntax so the consuming
constructor can select the type.
Integer aliases from these calls have block scope, including inside a runtime
`if`. The condition and runtime statements remain in the kernel.
Stored source procedures use their own entry point.

Import the scoped extensions after the upstream frontend modules used in a
file. In a `tl.swizzle2d` argument, write `tl.cast(tl.constexpr(n), tl.int64)`
so the integer type is preserved if Swizzle elaborates first. Its implicit
cast applies only to number literals already present when it captures arguments.
-/
namespace VeriTile.Dist.Frontend.TritonExt.Constexpr
open Lean Elab Term Meta
open VeriTile.Triton VeriTile.Triton.DSL

scoped syntax (name := constexprCall) "tl.constexpr" "(" tritonExpr ")" : tritonExpr
scoped syntax (name := shapeLenCall) "len(" tritonExpr ")" : tritonExpr
scoped syntax (name := nextPowerCall) "next_power_of_2(" tritonExpr ")" : tritonExpr

private abbrev SourceExpr := TSyntax `tritonExpr
private abbrev SourceStmt := TSyntax `tritonStmt

private inductive Value where
  | integer (n : Int)
  | boolean (b : Bool)
  | string (s : String)
  deriving BEq

private def literal : Value → MacroM SourceExpr
  | .integer n => do
    let lit : TSyntax `num := ⟨Syntax.mkNumLit (toString n.natAbs)⟩
    if n < 0 then `(tritonExpr| -$lit:num) else `(tritonExpr| $lit:num)
  | .boolean Bool.true => `(tritonExpr| true)
  | .boolean Bool.false => `(tritonExpr| false)
  | .string s =>
    let lit : TSyntax `str := ⟨Syntax.mkStrLit s⟩
    `(tritonExpr| $lit:str)

private def integerRegister (n : Int) : MacroM SourceExpr := do
  let dtype ←
    if -(2^31 : Int) ≤ n && n < 2^31 then `(tritonDType| tl.int32)
    else if 0 ≤ n && n < 2^32 then `(tritonDType| tl.uint32)
    else if -(2^63 : Int) ≤ n && n < 2^63 then `(tritonDType| tl.int64)
    else if 0 ≤ n && n < 2^64 then `(tritonDType| tl.uint64)
    else Macro.throwError "folded constexpr register exceeds Triton's integer range"
  let value ← literal (.integer n)
  `(tritonExpr| tl.cast($value:tritonExpr, $dtype:tritonDType))

-- SourceDType supplies canonical names. Use the source precision rather than
-- the interpreter carrier (for example uint8 and uint64 both use Nat).
private def width (name : String) : Option Nat := do
  let suffix ← ["tl.uint", "tl.int", "tl.bfloat", "tl.float"].findSome? fun stem =>
    if name.startsWith stem then some (name.drop stem.length).toString else none
  if ["8e4nv", "8e5"].contains suffix then some 8 else suffix.toNat?

private partial def nameOf (value : Expr) : TermElabM (Option Name) := do
  let value ← whnf value
  if value.isConstOf ``Name.anonymous then return some .anonymous
  if value.isAppOfArity ``Name.str 2 then
    let args := value.getAppArgs
    let some stem ← nameOf args[0]! | return none
    let .lit (.strVal suffix) ← whnf args[1]! | return none
    return some (.str stem suffix)
  return none

private structure Bindings where
  signatureNames : Option (List Name) := none
  constants : List (Name × SourceExpr) := []
  widths : List (Name × Nat) := []
  assigned : List Name := []
  runtime : List Name := []
  aliasNames : List Name := []

private def key (raw : Syntax) : Name := raw.getId.eraseMacroScopes

private partial def identifiers (raw : Syntax) : List Name :=
  if raw.isIdent then [key raw] else raw.getArgs.toList.flatMap identifiers

private partial def assignedNames (raw : Syntax) : List Name :=
  let args := raw.getArgs
  let own :=
    if args.size ≥ 2 && args[0]!.isAtom &&
        ["for", "tl.for", "tl.static_range"].contains args[0]!.getAtomVal.trimAscii.toString &&
        args[1]!.isIdent then [key args[1]!]
    else if let `(tritonStmt| $_:ident : tl.constexpr = $_:tritonExpr) := raw then []
    else if args.size ≥ 2 && args[0]!.isIdent then
      match args.findIdx? (fun arg => arg.isAtom &&
          ["=", ":=", "+=", "-=", "*=", "/=", "//=", "%="].contains arg.getAtomVal.trimAscii.toString) with
      | some index => (args.toList.take index).flatMap identifiers
      | none => []
    else []
  own ++ args.toList.flatMap assignedNames

private def bareBindings (stmts : Array SourceStmt) : Bindings := Id.run do
  let mut result : Bindings := { assigned := stmts.toList.flatMap (assignedNames ·.raw) }
  for stmt in stmts do
    match stmt with
    | `(tritonStmt| tl.region $ptr:ident = $dtype:tritonDType $[, $ps:ident = $ds:tritonDType]*) =>
      for (p,d) in (#[ptr] ++ ps).zip (#[dtype] ++ ds) do
        let name := key p.raw
        result := { result with runtime := name :: result.runtime }
        if let some bits := width (PythonFullConstructors.render d.raw) then
          result := { result with widths := (name,bits) :: result.widths }
    | `(tritonStmt| tl.param $id:ident : $_:tritonDType)
    | `(tritonStmt| tl.param $id:ident : $_:tritonDType (carrier=$_:tritonDType)) =>
      result := { result with runtime := key id.raw :: result.runtime }
    | _ => pure ()
  return result

private partial def listEntries (value : Expr) : TermElabM (List Expr) := do
  let value ← whnf value
  if value.isAppOfArity ``List.nil 1 then return []
  if value.isAppOfArity ``List.cons 3 then
    return value.getAppArgs[1]! :: (← listEntries value.getAppArgs[2]!)
  throwError "constexpr metadata must be a statically known list"

private def listedName (value : Expr) : TermElabM Name := do
  let .lit (.strVal name) ← whnf value | throwError "constexpr metadata names must be literal strings"
  return name.toName

private def pairedName (value : Expr) : TermElabM Name := do
  listedName (← mkAppM ``Prod.fst #[value])

private def signatureBindings (rawProfile : Syntax) (stmts : Array SourceStmt) : TermElabM Bindings := do
  let profile ← elabTermEnsuringType rawProfile (mkConst ``CallSignature)
  let names ← (← listEntries (← mkAppM ``CallSignature.constexpr #[profile])).mapM listedName
  let pointers ← listEntries (← mkAppM ``CallSignature.pointers #[profile])
  let floating ← listEntries (← mkAppM ``CallSignature.floatingPointers #[profile])
  let scalars ← listEntries (← mkAppM ``CallSignature.scalars #[profile])
  let sourceValues ← listEntries (← mkAppM ``CallSignature.sourceConstants #[profile])
  let env ← getEnv
  let constants ← sourceValues.mapM fun pair => do
    let name ← pairedName pair
    let .lit (.strVal value) ← whnf (← mkAppM ``Prod.snd #[pair])
      | throwError "source constant values must be literal strings"
    liftMacroM <| SourceBindings.constant env name.toString value
  let mut widths := []
  for pair in pointers do
    let dtype ← mkAppM ``Prod.snd #[pair]
    if let some dtype ← nameOf (← mkAppM ``SourceDType.dtypeName #[dtype]) then
      if let some bits := width dtype.toString then
        widths := (← pairedName pair, bits) :: widths
  return {
    signatureNames := some names
    constants, widths
    assigned := stmts.toList.flatMap (assignedNames ·.raw)
    runtime := ← (pointers ++ floating ++ scalars).mapM pairedName }

private def reducedValue (value : Expr) : TermElabM (Option Value) := do
  let value ← whnf value
  let ty ← whnf (← inferType value)
  if ty.isConstOf ``Nat then return (← getNatValue? value).map (fun n => .integer n)
  if ty.isConstOf ``Int then
    if let some n ← getIntValue? value then return some (.integer n)
    if value.isAppOfArity ``Int.ofNat 1 then
      return (← getNatValue? (← whnf value.appArg!)).map (fun n => .integer n)
    if value.isAppOfArity ``Int.negSucc 1 then
      return (← getNatValue? (← whnf value.appArg!)).map (fun n => .integer (-((n : Int) + 1)))
  if ty.isConstOf ``String then return (getStringValue? value).map Value.string
  if value.isConstOf ``Bool.true then return some (.boolean Bool.true)
  if value.isConstOf ``Bool.false then return some (.boolean Bool.false)
  return none

private def staticName (ctx : Bindings) (id : Ident) : TermElabM (Option Value) := do
  let name := key id.raw
  if ctx.assigned.contains name || ctx.runtime.contains name || ctx.aliasNames.contains name then
    return none
  match ctx.signatureNames with
  | some names =>
    unless names.contains name do return none
    let some value ← observing? (elabTerm id none) | return none
    reducedValue value
  | none =>
    let some decl := (← getLCtx).findFromUserName? name | return none
    reducedValue decl.toExpr

private partial def shapeLength (e : SourceExpr) (ctx : Bindings) : TermElabM Nat := do
  if let `(tritonExpr| ($inner:tritonExpr)) := e then return ← shapeLength inner ctx
  let `(tritonExpr| $shape:ident) := e
    | throwErrorAt e "len requires a statically bound tensor.shape"
  let .str owner "shape" := key shape.raw
    | throwErrorAt e "len requires a statically bound tensor.shape"
  unless owner != .anonymous && !(ctx.assigned.contains owner) do
    throwErrorAt e "len requires a statically bound tensor.shape"
  let some decl := (← getLCtx).findFromUserName? (Name.mkSimple (key shape.raw).toString)
    | throwErrorAt e "len requires a statically bound tensor.shape"
  unless ← isDefEq decl.type (mkApp (mkConst ``List [levelZero]) (mkConst ``Nat)) do
    throwErrorAt e "tensor.shape binding must have type List Nat"
  return (← listEntries decl.toExpr).length

private inductive SourceCall where
  | constexpr | rank | nextPower

private def call (raw : Syntax) : Option (SourceCall × SourceExpr) :=
  match raw with
  | `(tritonExpr| tl.constexpr($arg:tritonExpr)) => some (.constexpr, arg)
  | `(tritonExpr| len($arg:tritonExpr)) => some (.rank, arg)
  | `(tritonExpr| next_power_of_2($arg:tritonExpr)) => some (.nextPower, arg)
  | _ => none

private partial def containsCall (raw : Syntax) : Bool :=
  (call raw).isSome || raw.getArgs.any containsCall

private partial def aliasDeclarations (raw : Syntax) : List (Name × Bool) :=
  match raw with
  | `(tritonStmt| $id:ident : tl.constexpr = $value:tritonExpr) =>
    [(key id.raw, containsCall value.raw)]
  | _ => raw.getArgs.toList.flatMap aliasDeclarations

private def shadows (ctx : Bindings) (name : Name) : Bool :=
  ctx.assigned.contains name || ctx.runtime.contains name || ctx.aliasNames.contains name ||
  ctx.constants.any (·.1 == name) || ctx.signatureNames.any (·.contains name)

private partial def evaluate (ctx : Bindings) (e : SourceExpr) : TermElabM (Option Value) := do
  if e.raw.getKind == choiceKind then return ← evaluate ctx ⟨e.raw[0]!⟩
  if let some (callee,arg) := call e.raw then
    match callee with
    | .constexpr =>
      let some value ← evaluate ctx arg | throwErrorAt arg "tl.constexpr requires a statically known value"
      return some value
    | .rank =>
      if shadows ctx `len then throwErrorAt e "len must name the Python builtin"
      return some (.integer (← shapeLength arg ctx))
    | .nextPower =>
      if shadows ctx `next_power_of_2 then
        throwErrorAt e "next_power_of_2 must name the imported constexpr helper"
      let some (.integer n) ← evaluate ctx arg
        | throwErrorAt arg "next_power_of_2 requires a statically known integer"
      unless 0 ≤ n && n ≤ 2^64 do
        throwErrorAt arg "next_power_of_2 requires an integer in [0, 2^64]"
      return some (.integer (if n == 0 then 0 else n.toNat.nextPowerOfTwo))
  match e with
  | `(tritonExpr| $n:num) => return some (.integer n.getNat)
  | `(tritonExpr| $s:str) => return some (.string s.getString)
  | `(tritonExpr| true) => return some (.boolean Bool.true)
  | `(tritonExpr| false) => return some (.boolean Bool.false)
  | `(tritonExpr| ($inner:tritonExpr)) => evaluate ctx inner
  | `(tritonExpr| -$arg:tritonExpr) =>
    return (← evaluate ctx arg).bind fun
      | .integer n => some (.integer (-n))
      | _ => none
  | `(tritonExpr| $lhs:tritonExpr // $rhs:tritonExpr) =>
    let some (.integer lhs) ← evaluate ctx lhs | return none
    let some (.integer rhs) ← evaluate ctx rhs | return none
    if rhs == 0 then throwErrorAt e "constexpr integer division by zero"
    return some (.integer (if rhs > 0 then lhs / rhs else (-lhs) / (-rhs)))
  | `(tritonExpr| $id:ident) =>
    let name := key id.raw
    if let .str (.str (.str ptr "dtype") "element_ty") "primitive_bitwidth" := name then
      if ctx.assigned.contains ptr then return none
      return (ctx.widths.lookup ptr).map (fun n => .integer n)
    if let some value := ctx.constants.lookup name then
      return ← evaluate { ctx with constants := [] } value
    staticName ctx id
  | _ => return none

/-- Resolve a Boolean with the same immutable source bindings as `tl.constexpr`. -/
def resolveBool (profile : Option Syntax) (stmts : Array (TSyntax `tritonStmt))
    (expression : TSyntax `tritonExpr) : TermElabM (Option Bool) := do
  let ctx ← match profile with
    | some signature => signatureBindings signature stmts
    | none => pure (bareBindings stmts)
  let aliases := stmts.toList.flatMap (aliasDeclarations ·.raw)
  let some (.boolean value) ← evaluate { ctx with aliasNames := aliases.map Prod.fst } expression
    | return none
  return some value

mutual

private partial def lower (ctx : Bindings) (aliases : List Name) (raw : Syntax) :
    TermElabM Syntax := do
  if raw.getKind == choiceKind && containsCall raw then return ← lower ctx aliases raw[0]!
  match raw with
  | `(tritonStmt| $id:ident = $value:tritonExpr) =>
    if containsCall value.raw || (identifiers value.raw).any aliases.contains then
      if let some (.integer n) ← evaluate ctx value then
        let value ← liftMacroM (integerRegister n)
        return (← liftMacroM `(tritonStmt| $id:ident = $value)).raw
  | `(tritonStmt| if $c:tritonExpr { $yes:tritonStmt* } else { $no:tritonStmt* })
  | `(tritonStmt| tl.if $c:tritonExpr { $yes:tritonStmt* } else { $no:tritonStmt* }) =>
    let condition : SourceExpr := ⟨← lower ctx aliases c.raw⟩
    let yes ← lowerBlock ctx aliases yes
    let no ← lowerBlock ctx aliases no
    if raw[0]!.getAtomVal.trimAscii.toString == "tl.if" then
      return (← liftMacroM `(tritonStmt| tl.if $condition { $yes* } else { $no* })).raw
    return (← liftMacroM `(tritonStmt| if $condition { $yes* } else { $no* })).raw
  | `(tritonStmt| if $c:tritonExpr { $yes:tritonStmt* })
  | `(tritonStmt| tl.if $c:tritonExpr { $yes:tritonStmt* }) =>
    let condition : SourceExpr := ⟨← lower ctx aliases c.raw⟩
    let yes ← lowerBlock ctx aliases yes
    if raw[0]!.getAtomVal.trimAscii.toString == "tl.if" then
      return (← liftMacroM `(tritonStmt| tl.if $condition { $yes* })).raw
    return (← liftMacroM `(tritonStmt| if $condition { $yes* })).raw
  | _ => pure ()
  if let some _ := call raw then
    let some value ← evaluate ctx ⟨raw⟩ | throwErrorAt raw "unresolved constexpr call"
    return (← liftMacroM (literal value)).raw
  if let `(tritonExpr| $_:tritonExpr // $_:tritonExpr) := raw then
    if containsCall raw then
      if let some result ← evaluate ctx ⟨raw⟩ then
        return (← liftMacroM (literal result)).raw
  if let `(tritonExpr| $id:ident) := raw then
    if aliases.contains (key id.raw) then
      if let some value := ctx.constants.lookup (key id.raw) then return value.raw
      throwErrorAt id "constexpr alias is not in scope"
  if let `(tritonStmt| tl.static_assert($pred:tritonExpr $[, $message:str]?)) := raw then
    if containsCall pred.raw then
      let `(tritonExpr| $left:tritonExpr == $right:tritonExpr) := pred
        | throwErrorAt pred "constexpr static assertion requires a static equality"
      let some a ← evaluate ctx left
        | throwErrorAt left "constexpr static assertion requires a static equality"
      let some b ← evaluate ctx right
        | throwErrorAt right "constexpr static assertion requires a static equality"
      unless a == b do throwErrorAt pred "constexpr static assertion failed"
      return (← liftMacroM `(tritonStmt| tl.static_assert(true $[, $message:str]?))).raw
  if let `(tritonStmt| $_:ident : tl.constexpr = $value:tritonExpr) := raw then
    if containsCall value.raw then throwErrorAt raw "constexpr helper alias requires a block or if branch"
  return raw.setArgs (← raw.getArgs.mapM (lower ctx aliases))

private partial def lowerBlock (ctx : Bindings) (aliases : List Name)
    (stmts : Array SourceStmt) : TermElabM (Array SourceStmt) := do
  let mut ctx := ctx
  let mut lowered := #[]
  for stmt in stmts do
    if let `(tritonStmt| $id:ident : tl.constexpr = $value:tritonExpr) := stmt then
      if containsCall value.raw then
        let name := key id.raw
        if (ctx.aliasNames.count name != 1) || ctx.assigned.contains name || ctx.runtime.contains name ||
            (ctx.constants.lookup name).isSome || ctx.signatureNames.any (·.contains name) then
          throwErrorAt id "constexpr alias must be immutable and distinct"
        let some (.integer n) ← evaluate ctx value
          | throwErrorAt value "constexpr aliases require a static integer"
        let lit ← liftMacroM (literal (.integer n))
        ctx := { ctx with constants := (name,lit) :: ctx.constants }
        continue
    lowered := lowered.push ⟨← lower ctx aliases stmt.raw⟩
  return lowered

end

private def prepare (ctx : Bindings) (stmts : Array SourceStmt) : TermElabM (Array SourceStmt) := do
  let declarations := stmts.toList.flatMap (aliasDeclarations ·.raw)
  let aliases := declarations.filterMap (fun (name, extended) => if extended then some name else none)
  lowerBlock { ctx with aliasNames := declarations.map Prod.fst } aliases stmts

@[term_elab VeriTile.Triton.DSL.tritonBlock]
def elaborateBlock : TermElab := fun stx expected => do
  let `(triton { $stmts:tritonStmt* }) := stx | throwUnsupportedSyntax
  unless stmts.any (containsCall ·.raw) do throwUnsupportedSyntax
  let lowered ← prepare (bareBindings stmts) stmts
  elabTerm (← liftMacroM `(triton { $lowered* })) expected

@[term_elab VeriTile.Triton.DSL.CallSignature.withSignature,
  term_elab VeriTile.Triton.DSL.CallSignature.withCall]
def elaborateSource : TermElab := fun stx expected => do
  let original := stx.getArgs.back!
  let .ok normalized := RawSourceText.normalize original.getAtomVal | throwUnsupportedSyntax
  let .ok parsed := Parser.runParserCategory (← getEnv) `term ("triton {\n" ++ normalized ++ "\n}")
    | throwUnsupportedSyntax
  let `(triton { $stmts:tritonStmt* }) := parsed | throwUnsupportedSyntax
  unless stmts.any (containsCall ·.raw) do throwUnsupportedSyntax
  let lowered ← prepare (← signatureBindings stx[1] stmts) stmts
  let source := String.intercalate "\n" (lowered.toList.map (PythonFullConstructors.render ·.raw))
  let replacement := Syntax.atom original.getHeadInfo ("{\n" ++ source ++ "\n}")
  elabTerm (stx.setArgs (stx.getArgs.set! (stx.getArgs.size-1) replacement)) expected

end VeriTile.Dist.Frontend.TritonExt.Constexpr
