-- Source: ByteDance-Seed/Triton-distributed@7908e4ea9010bb2238f9f05b28c904fd4b71c60a python/triton_dist/kernels/nvidia/allgather_group_gemm.py:534-541; ByteDance-Seed/Triton-distributed@7908e4ea9010bb2238f9f05b28c904fd4b71c60a python/triton_dist/kernels/nvidia/moe_reduce_ar.py:47-57; ByteDance-Seed/Triton-distributed@7908e4ea9010bb2238f9f05b28c904fd4b71c60a python/triton_dist/kernels/nvidia/moe_reduce_rs.py:124-134; ByteDance-Seed/Triton-distributed@7908e4ea9010bb2238f9f05b28c904fd4b71c60a tutorials/04-deepseek-infer-all2all.py:78-79; ByteDance-Seed/Triton-distributed@7908e4ea9010bb2238f9f05b28c904fd4b71c60a python/triton_dist/kernels/nvidia/common_ops.py:53-57; ByteDance-Seed/Triton-distributed@7908e4ea9010bb2238f9f05b28c904fd4b71c60a python/triton_dist/kernels/nvidia/all_to_all_single_2d.py:35-39
-- Licence: MIT
-- Changes: transcribed to Lean; instantiate the pinned scalar and tuple results at their lexical call sites
import VeriTile.Dist.Frontend.TritonExt.SignedSum
import VeriTile.Dist.Frontend.TritonExt.Range
import VeriTile.Triton.DSL.StatementJitFunctions

namespace VeriTile.Dist.Frontend.TritonExt.SourceHelpers
open Lean Elab Term Meta
open VeriTile.Triton VeriTile.Triton.DSL

/-- These bindings also work directly in the upstream public jit_functions list. -/
def ceilDiv : StatementJitFunction := triton_function (a, b) constexpr_args [] {
  return (a + b - 1) // b
}

def swizzleM : StatementJitFunction := triton_function (tile_id, num_pid_m, num_pid_n, GROUP_SIZE_M)
    constexpr_args [GROUP_SIZE_M] {
  num_pid_in_group = GROUP_SIZE_M * num_pid_n
  group_id = tile_id // num_pid_in_group
  first_pid_m = group_id * GROUP_SIZE_M
  group_size_m = min(num_pid_m - first_pid_m, GROUP_SIZE_M)
  pid_m = first_pid_m + (tile_id % group_size_m)
  pid_n = (tile_id % num_pid_in_group) // group_size_m
  return pid_m, pid_n
}

def swizzleN : StatementJitFunction := triton_function (pid, nblocks_m, nblocks_n, GROUP_SIZE_N)
    constexpr_args [GROUP_SIZE_N] {
  nblocks_per_group = GROUP_SIZE_N * nblocks_m
  group_id = pid // nblocks_per_group
  remainder = pid - group_id * nblocks_per_group
  pid_m = remainder // GROUP_SIZE_N
  pid_n = remainder % GROUP_SIZE_N + group_id * GROUP_SIZE_N
  return pid_m, pid_n, group_id
}

/-- Explicit source binding. The ordinary DSL keeps ownership of all other names. -/
scoped syntax (name := sourceHelpers) "with_local_jit_helpers " "in " term:lead : term

scoped syntax (name := gpuMasterCall) "_is_gpu_master(" ")" : tritonExpr
scoped syntax (name := ctaMasterCall) "_is_cta_master(" ")" : tritonExpr

private abbrev Argument := TSyntax `statementJitArgument
private abbrev Operand := TSyntax `tritonExpr

private def bindActuals (params : List String) (args : Array Argument) :
    TermElabM (List (String × Operand)) := do
  let mut bound := []
  let mut named := Bool.false
  for arg in args do
    let (key, value) ← match arg with
      | `(statementJitArgument| $k:ident = $v:tritonExpr) => do
        named := Bool.true
        pure (k.getId.toString, v)
      | `(statementJitArgument| $v:tritonExpr) => do
        if named then throwErrorAt arg "local helper: positional argument after keyword"
        let some key := params[bound.length]? | throwErrorAt arg "local helper: too many arguments"
        pure (key, v)
      | _ => throwErrorAt arg "unsupported local helper argument"
    unless params.contains key do throwErrorAt arg "local helper: unknown keyword {key}"
    if bound.any (·.1 == key) then throwErrorAt arg "local helper: repeated argument {key}"
    bound := bound ++ [(key, value)]
  unless bound.length == params.length do throwError "local helper: missing argument"
  return bound

private partial def ids (s : Syntax) : List Name :=
  if s.isIdent then [s.getId.eraseMacroScopes] else s.getArgs.toList.flatMap ids

private abbrev Rewrite := StateT (List Name) TermElabM

private def fresh : Rewrite Ident := do
  let used ← get
  let mut n := 0
  while used.contains (Name.mkSimple ("vt_helper_" ++ toString n)) do n := n + 1
  let name := Name.mkSimple ("vt_helper_" ++ toString n)
  set (name :: used)
  return mkIdent name

private partial def substitute (bindings : List (Name × Ident)) (s : Syntax) : Syntax :=
  if s.isIdent then (bindings.lookup s.getId.eraseMacroScopes).map (·.raw) |>.getD s
  else s.setArgs (s.getArgs.map (substitute bindings))

-- Only the two closed, validated arithmetic bodies above enter this path.
-- Snapshot runtime arguments in source order, then alpha-rename the local writes.
private def tupleBody (f : StatementJitFunction) (args : Array Argument) (dst : Array Ident)
    (constants : List Name) : Rewrite (Array Syntax) := do
  let actuals ← bindActuals f.parameters args
  let mut names : List (Name × Ident) := []
  let mut out := #[]
  for (formal, value) in actuals do
    if f.constexpr.contains formal then
      let `(tritonExpr| $arg:ident) := value | throwErrorAt value "local helper expects a caller constexpr"
      unless constants.contains arg.getId.eraseMacroScopes do
        throwErrorAt value "local helper expects a caller constexpr"
      names := (formal.toName, arg) :: names
    else
      let arg ← fresh
      out := out.push (← `(tritonStmt| $arg:ident = $value:tritonExpr)).raw
      names := (formal.toName, arg) :: names
  let .ok parsed := Parser.runParserCategory (← getEnv) `term ("triton {\n" ++ f.source ++ "\n}")
    | throwError "invalid pinned helper source"
  let `(triton { $body:tritonStmt* }) := parsed | throwError "invalid pinned helper block"
  for stmt in body.pop do
    let `(tritonStmt| $id:ident = $value:tritonExpr) := stmt | throwError "invalid pinned helper assignment"
    let localId ← fresh
    let value : Operand := ⟨substitute names value.raw⟩
    out := out.push (← `(tritonStmt| $localId:ident = $value:tritonExpr)).raw
    names := (id.getId.eraseMacroScopes, localId) :: names
  let `(tritonStmt| return $results:tritonExpr,*) := body.back! | throwError "invalid pinned helper return"
  unless dst.size == results.getElems.size do throwError "local helper: return arity mismatch"
  for (d,v) in dst.zip results.getElems do
    let value : Operand := ⟨substitute names v.raw⟩
    out := out.push (← `(tritonStmt| $d:ident = $value:tritonExpr)).raw
  return out

private def call? (s : Syntax) : Option (Name × Array Argument) := do
  let `(tritonExpr| $name:ident($args:statementJitArgument,*)) := s | none
  return (name.getId.eraseMacroScopes, args.getElems)

private def gpuPredicate : TermElabM Syntax := do
  return (← `(tritonExpr| ((tl.program_id(axis=0) + tl.program_id(axis=1) + tl.program_id(axis=2)) == 0))).raw

private partial def lower (s : Syntax) (constants : List Name) : Rewrite (Array Syntax) := do
  if s.isOfKind ``gpuMasterCall then
    return #[← gpuPredicate]
  if s.isOfKind ``ctaMasterCall then throwError "local helper _is_cta_master requires the SIMT tid binding (#81)"
  if s.getKind == choiceKind then
    -- Prefer the generic checked call/tuple production over built-in parser alternatives.
    for alt in s.getArgs do
      if alt.isOfKind ``StatementJitFunctions.helperTupleCall ||
          alt.isOfKind ``StatementJitFunctions.helperCall then
        return ← lower alt constants
    return ← lower s[0]! constants
  if let `(tritonStmt| $a:ident, $b:ident $[, $rest:ident]* = $fn:ident($args:statementJitArgument,*)) := s then
    let f? := match fn.getId.eraseMacroScopes.toString with
      | "swizzle_2d" => some swizzleM
      | "swizzle_2d_by_group_n" => some swizzleN
      | _ => none
    if let some f := f? then return ← tupleBody f args.getElems (#[a,b] ++ rest) constants
  if let some (name,args) := call? s then
    if name == `ceil_div then
      let actuals ← bindActuals ceilDiv.parameters args
      -- The pinned loop bounds read two scalar names. Restrict this expression form
      -- to those immutable reads at this point, so repeating b cannot repeat a load.
      let some a := actuals.lookup "a" | throwError "ceil_div: missing a"
      let some b := actuals.lookup "b" | throwError "ceil_div: missing b"
      let `(tritonExpr| $a:ident) := a | throwError "nested ceil_div requires two scalar names"
      let `(tritonExpr| $b:ident) := b | throwError "nested ceil_div requires two scalar names"
      return #[(← `(tritonExpr| (($a:ident + $b:ident - 1) // $b:ident))).raw]
    if name == `_is_gpu_master then
      let _ ← bindActuals [] args
      return #[← gpuPredicate]
    if name == `_is_cta_master then throwError "local helper _is_cta_master requires the SIMT tid binding (#81)"
  let mut args := #[]
  for arg in s.getArgs do args := args ++ (← lower arg constants)
  return #[s.setArgs args]

private partial def stringNames (e : Expr) : TermElabM (List Name) := do
  let e ← whnf e
  if e.isAppOfArity ``List.nil 1 then return []
  if e.isAppOfArity ``List.cons 3 then
    let .lit (.strVal s) ← whnf e.getAppArgs[1]! | throwError "expected literal parameter name"
    return s.toName :: (← stringNames e.getAppArgs[2]!)
  throwError "local helpers require static call-signature metadata"

/-- Reserve every ABI identifier, including ports absent from the caller text. -/
def signatureNames (signature : Syntax) : TermElabM (List Name × List Name) := do
  let profile ← elabTermEnsuringType signature (mkConst ``CallSignature)
  let constants ← stringNames (← mkAppM ``CallSignature.constexpr #[profile])
  let mut occupied := constants
  for field in [``CallSignature.pointers, ``CallSignature.floatingPointers, ``CallSignature.scalars] do
    let pairs ← mkAppM field #[profile]
    let type ← inferType pairs
    let pairType := type.getAppArgs[0]!
    let fstProj ← withLocalDeclD `p pairType fun x => do mkLambdaFVars #[x] (← mkAppM ``Prod.fst #[x])
    occupied := (← stringNames (← mkAppM ``List.map #[fstProj, pairs])) ++ occupied
  return (constants, occupied)

@[term_elab sourceHelpers] def elaborateHelpers : TermElab := fun wrapper expected => do
  let caller := wrapper[2]
  let raw := caller.getArgs.back!
  let mut constants := []
  let mut occupied := ids caller
  if caller.isOfKind ``CallSignature.withCall || caller.isOfKind ``CallSignature.withSignature then
    let (names, abi) ← signatureNames caller[1]
    constants := names
    occupied := abi ++ occupied
  else if caller.isOfKind ``SourceProcedures.sourceParams || caller.isOfKind ``SourceProcedures.sourceProcedure then
    constants := caller[6].getSepArgs.toList.map (·.getId.eraseMacroScopes)
  else throwErrorAt caller "use local JIT helpers with a pasted call signature or source procedure"
  let .ok source := RawSourceText.normalize raw.getAtomVal | throwErrorAt raw "invalid local helper source"
  let parsed ← match Parser.runParserCategory (← getEnv) `term ("triton {\n" ++ source ++ "\n}") with
    | .ok body => pure body
    | .error e => throwErrorAt raw "{e}"
  let parsed ← if caller.isOfKind ``CallSignature.withCall &&
      (source.contains "get_element_at" || source.contains "tl.cumsum" || source.contains "tl.sum" || source.contains "tl.cdiv") then do
    let (next, _) ← SignedSum.prepare caller[1] parsed fun arg => do
      let some (name, args) := call? arg | return none
      unless name == `get_element_at do return none
      let bindings ← bindActuals ["tensor", "idx"] args
      return (Prod.mk <$> bindings.lookup "tensor" <*> bindings.lookup "idx")
    pure next
  else pure parsed
  let (expanded, _) ← (lower parsed constants).run ((ids parsed ++ occupied ++ constants).eraseDups)
  let `(triton { $body:tritonStmt* }) := expanded[0]! | throwError "invalid expanded caller"
  let text := String.intercalate "\n" (body.toList.map (PythonFullConstructors.render ·.raw))
  let repl := Syntax.atom raw.getHeadInfo ("{\n" ++ text ++ "\n}")
  elabTerm (caller.setArgs (caller.getArgs.set! (caller.getArgs.size - 1) repl)) expected

@[term_elab VeriTile.Triton.DSL.CallSignature.withCall] def elaborateSigned : TermElab := SignedSum.elaborate

end VeriTile.Dist.Frontend.TritonExt.SourceHelpers
