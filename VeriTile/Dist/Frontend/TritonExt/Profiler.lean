import VeriTile.Dist.Frontend.TritonExt.Constexpr

/-!
Disabled profiler records for the retained Triton-distributed all-to-all
kernels at 7908e4ea9010bb2238f9f05b28c904fd4b71c60a.
Under `python/triton_dist/kernels/nvidia/`, the three bindings and first
records occur in `all_to_all_vdev_2d_offset.py:221–227,245`,
`all_to_all_vdev_2d_offset.py:310–316,340`, and
`all_to_all_vdev_2d_offset_inter_node.py:100–106,136`.

The scoped spelling `Profiler.create` denotes the pinned imported constructor,
and `tid(0)` in its leader expression denotes the pinned thread-ID query.
In `python/triton_dist/tools/profiler/language.py:52–93` all buffer writes are
guarded by `ENABLE_PROFILING`. In `language.py:152–169` the same guard encloses
all record effects, and the returned profiler fields are unchanged otherwise.
The adapter erases that constructor with the three kernels' pure arguments,
then erases discarded records and self-assignments of the bound profiler.
A runtime condition surrounding a record remains in the kernel.

The profiling flag must resolve to false using the constexpr bindings. Only
record statements may use the profiler after construction, including inside
control flow. This keeps the discarded buffer and metadata unobservable.
The constructor and record keyword atoms are scoped.
-/
namespace VeriTile.Dist.Frontend.TritonExt.Profiler
open Lean Elab Term
open VeriTile.Triton.DSL

scoped syntax (name := profilerCreate)
  ident " = " "Profiler.create(" tritonKwarg,* ")" : tritonStmt
scoped syntax (name := profilerRecordAssign)
  ident " = " ident "(" "is_start=" tritonExpr "," "task_type=" tritonExpr ")" : tritonStmt
scoped syntax (name := profilerRecordStmt)
  ident "(" "is_start=" tritonExpr "," "task_type=" tritonExpr ")" : tritonStmt

private abbrev SourceStmt := TSyntax `tritonStmt
private abbrev SourceExpr := TSyntax `tritonExpr

private def sourceName (id : Syntax) : Name := id.getId.eraseMacroScopes

private def isProfilerNode (raw : Syntax) : Bool :=
  raw.getKind == ``profilerCreate || raw.getKind == ``profilerRecordAssign ||
    raw.getKind == ``profilerRecordStmt

private def selectProfilerNode (raw : Syntax) : Syntax :=
  if raw.getKind == choiceKind then (raw.getArgs.find? isProfilerNode).getD raw else raw

private partial def containsProfiler (raw : Syntax) : Bool :=
  isProfilerNode raw || raw.getArgs.any containsProfiler

private def bindingName (stmt : SourceStmt) : Option Name :=
  match selectProfilerNode stmt.raw with
  | `(tritonStmt| $id:ident = Profiler.create($_:tritonKwarg,*)) => some (sourceName id.raw)
  | _ => none

private def createArgs (args : Array (TSyntax `tritonKwarg)) :
    TermElabM (List (String × SourceExpr)) :=
  args.toList.mapM fun arg => do
    let `(tritonKwarg| $key:ident = $value:tritonExpr) := arg
      | throwErrorAt arg "expected a named profiler constructor argument"
    return ((sourceName key.raw).toString, value)

private def isLeaderArg (expression : SourceExpr) : Bool :=
  match expression with
  | `(tritonExpr| true) | `(tritonExpr| false) => Bool.true
  | `(tritonExpr| ($function:ident(0) == 0)) => sourceName function.raw == `tid
  | _ => Bool.false

private def checkConstructor (profile : Option Syntax) (body : Array SourceStmt)
    (raw : Syntax) (names : List Name) (args : Array (TSyntax `tritonKwarg)) :
    TermElabM Unit := do
  let [("profiler_buffer", buffer), ("group_id", group), ("num_groups", count),
      ("is_leader", leader), ("ENABLE_PROFILING", flag)] ← createArgs args
    | throwErrorAt raw "expected the pinned named arguments to Profiler.create"
  let `(tritonExpr| $bufferName:ident) := buffer
    | throwErrorAt buffer "profiler_buffer must be a plain source name"
  let .str .anonymous _ := sourceName bufferName.raw
    | throwErrorAt buffer "profiler_buffer must be a plain source name"
  if names.contains (sourceName bufferName.raw) then
    throwErrorAt buffer "a profiler cannot be used as a profiler buffer"
  unless (match group with | `(tritonExpr| 0) => Bool.true | _ => Bool.false) &&
      (match count with | `(tritonExpr| 1) => Bool.true | _ => Bool.false) &&
      isLeaderArg leader do
    throwErrorAt raw "Profiler.create requires group_id=0, num_groups=1 and a pure leader expression"
  match ← Constexpr.resolveBool profile body flag with
  | some Bool.false => pure ()
  | some Bool.true => throwErrorAt flag "profiler recording requires ENABLE_PROFILING=False"
  | none => throwErrorAt flag "ENABLE_PROFILING must be a statically known Boolean"

private def checkRecord (bound : List Name) (target : Option Ident) (method : Ident)
    (start task : SourceExpr) : TermElabM Unit := do
  let .str receiver "record" := sourceName method.raw
    | throwErrorAt method "expected a bound profiler's record method"
  unless bound.contains receiver do
    throwErrorAt method "record receiver is not bound as a profiler"
  if let some id := target then
    unless sourceName id.raw == receiver do
      throwErrorAt id "profiler.record assignment must preserve its receiver"
  match start, task with
  | `(tritonExpr| true), `(tritonExpr| $_:num)
  | `(tritonExpr| false), `(tritonExpr| $_:num) => pure ()
  | _, _ => throwErrorAt method "profiler.record requires Boolean and integer literal arguments"

private partial def lower (names bound : List Name) (raw : Syntax) :
    TermElabM (Array Syntax) := do
  let raw := selectProfilerNode raw
  match raw with
  | `(tritonStmt| $id:ident = $method:ident(is_start=$start:tritonExpr, task_type=$task:tritonExpr)) =>
    checkRecord bound (some id) method start task
    return #[]
  | `(tritonStmt| $method:ident(is_start=$start:tritonExpr, task_type=$task:tritonExpr)) =>
    checkRecord bound none method start task
    return #[]
  | `(tritonStmt| $_:ident = Profiler.create($_:tritonKwarg,*)) =>
    throwErrorAt raw "profiler binding must be declared at kernel top level"
  | _ => pure ()
  let args := raw.getArgs
  if args.size ≥ 2 && args[0]!.isAtom && args[1]!.isIdent &&
      ["tl.source_helper", "tl.source_alias"].contains args[0]!.getAtomVal.trimAscii.toString &&
      sourceName args[1]! == `tid then
    throwErrorAt raw "the profiler leader requires the pinned tid helper"
  if raw.isIdent && names.any (·.isPrefixOf (sourceName raw)) then
    throwErrorAt raw "a profiler may only be used by its record statements"
  let args ← args.foldlM (fun acc arg => return acc ++ (← lower names bound arg)) #[]
  return #[raw.setArgs args]

private def prepare (profile : Option Syntax) (body : Array SourceStmt) :
    TermElabM (Array SourceStmt) := do
  unless body.any (containsProfiler ·.raw) do throwUnsupportedSyntax
  let names := body.toList.filterMap bindingName
  let mut bound := []
  let mut result := #[]
  for stmt in body do
    let raw := selectProfilerNode stmt.raw
    if let `(tritonStmt| $id:ident = Profiler.create($args:tritonKwarg,*)) := raw then
      let name := sourceName id.raw
      let .str .anonymous _ := name
        | throwErrorAt id "profiler binding must be a plain source name"
      if bound.contains name then throwErrorAt id "profiler binding must be unique"
      checkConstructor profile body raw names args.getElems
      bound := name :: bound
    else
      result := result ++ (← lower (`Profiler :: names) bound raw).map (⟨·⟩)
  return result

@[term_elab VeriTile.Triton.DSL.tritonBlock]
def elaborateBlock : TermElab := fun stx expected => do
  let `(triton { $body:tritonStmt* }) := stx | throwUnsupportedSyntax
  let lowered ← prepare none body
  elabTerm (← liftMacroM `(triton { $lowered* })) expected

@[term_elab VeriTile.Triton.DSL.CallSignature.withSignature,
  term_elab VeriTile.Triton.DSL.CallSignature.withCall]
def elaborateSource : TermElab := fun stx expected => do
  let raw := stx.getArgs.back!
  let .ok source := RawSourceText.normalize raw.getAtomVal | throwUnsupportedSyntax
  let .ok parsed := Parser.runParserCategory (← getEnv) `term ("triton {\n" ++ source ++ "\n}")
    | throwUnsupportedSyntax
  let `(triton { $body:tritonStmt* }) := parsed | throwUnsupportedSyntax
  let lowered ← prepare (some stx[1]) body
  let source := String.intercalate "\n" (lowered.toList.map (PythonFullConstructors.render ·.raw))
  let replacement := Syntax.atom raw.getHeadInfo ("{\n" ++ source ++ "\n}")
  elabTerm (stx.setArgs (stx.getArgs.set! (stx.getArgs.size - 1) replacement)) expected

end VeriTile.Dist.Frontend.TritonExt.Profiler
