-- Source: ByteDance-Seed/Triton-distributed@7908e4ea9010bb2238f9f05b28c904fd4b71c60a python/triton_dist/kernels/nvidia/reduce_scatter.py:181-203; ByteDance-Seed/Triton-distributed@7908e4ea9010bb2238f9f05b28c904fd4b71c60a python/triton_dist/kernels/nvidia/all_to_all_vdev_2d_offset_inter_node.py:46-66
-- Licence: MIT
-- Changes: transcribed to Lean; bind three sequential source procedures at their calling statement
import VeriTile.Dist.Frontend.TritonExt.SourceHelpers
import VeriTile.Triton.DSL.PythonFullConstructors

/-! Bind three pinned sequential memory procedures at a lexical callsite.
Each declaration uses the existing checked source-procedure interface. The
caller expands stable names and numeric literals, freshens callee registers,
and delegates the complete caller to the ordinary typed kernel elaborator.
The output-pointer conditional from the ring kernels selects exactly one body.
-/
namespace VeriTile.Dist.Frontend.TritonExt.ProcedureHelpers
open VeriTile.Triton VeriTile.Triton.DSL
open Lean Elab Term Meta

def copyContinuous : SourceProcedure :=
  with_triton_params (src_ptr, dst_ptr, N, BLOCK_SIZE) constexpr_args [BLOCK_SIZE] in triton {
    pid = tl.program_id(axis=0)
    n_blocks = tl.cdiv(N, BLOCK_SIZE)
    num_pid = tl.num_programs(axis=0)
    for n in range(pid, n_blocks, num_pid):
      offs = n * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
      mask = offs < N
      val = tl.load(src_ptr + offs, mask)
      tl.store(dst_ptr + offs, val, mask)
  }

def addContinuous : SourceProcedure :=
  with_triton_params (lhs_ptr, rhs_ptr, out_ptr, N, BLOCK_SIZE) constexpr_args [BLOCK_SIZE] in triton {
    pid = tl.program_id(axis=0)
    n_blocks = tl.cdiv(N, BLOCK_SIZE)
    num_pid = tl.num_programs(axis=0)
    for n in range(pid, n_blocks, num_pid):
      offs = n * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
      mask = offs < N
      lhs = tl.load(lhs_ptr + offs, mask)
      rhs = tl.load(rhs_ptr + offs, mask)
      tl.store(out_ptr + offs, lhs + rhs, mask)
  }

def transpose : SourceProcedure :=
  with_triton_params (ptr_x, ptr_y, M, N, BLOCK_M, BLOCK_N) constexpr_args [BLOCK_M, BLOCK_N] in triton {
    n_block_m = tl.cdiv(M, BLOCK_M)
    n_block_n = tl.cdiv(N, BLOCK_N)
    for bid in range(n_block_m * n_block_n):
      pid_m = bid // n_block_n
      pid_n = bid % n_block_n
      rm = pid_m * BLOCK_M + tl.arange(0, BLOCK_M)
      rn = pid_n * BLOCK_N + tl.arange(0, BLOCK_N)
      mask_x = (rm[:, None] < M) & (rn[None, :] < N)
      offs_x = rm[:, None] * N + rn[None, :]
      val = tl.load(ptr_x + offs_x, mask=mask_x, other=0.0)
      val_t = tl.trans(val)
      row_y = rn
      col_y = rm
      mask_y = (row_y[:, None] < N) & (col_y[None, :] < M)
      offs_y = row_y[:, None] * M + col_y[None, :]
      tl.store(ptr_y + offs_y, val_t, mask=mask_y)
  }

private abbrev Statement := TSyntax `tritonStmt
private abbrev Value := TSyntax `tritonExpr
private abbrev Arguments := List (Name × Value)

private def binding : Name → Option (SourceProcedure × List Name)
  | `copy_continuous_kernel => some (copyContinuous, [`pid,`n_blocks,`num_pid,`n,`offs,`mask,`val])
  | `add_continuous_kernel => some (addContinuous, [`pid,`n_blocks,`num_pid,`n,`offs,`mask,`lhs,`rhs])
  | `transpose_kernel => some (transpose, [`n_block_m,`n_block_n,`bid,`pid_m,`pid_n,`rm,`rn,
      `mask_x,`offs_x,`val,`val_t,`row_y,`col_y,`mask_y,`offs_y])
  | _ => none

private def parseBody (raw : String) : TermElabM (Array Statement) := do
  let .ok source := RawSourceText.normalize raw | throwError "invalid procedure block"
  let .ok parsed := Parser.runParserCategory (← getEnv) `term ("triton {\n" ++ source ++ "\n}")
    | throwError "cannot parse sequential procedure caller"
  let `(triton { $body:tritonStmt* }) := parsed | throwError "expected a complete procedure block"
  return body

-- The pinned output-pointer conditional is a single procedure argument.
-- Keeping this spelling in the call grammar avoids reinterpreting a following
-- statement-level if as part of the preceding assignment.
scoped syntax tritonExpr " if " tritonExpr " else " tritonExpr : statementJitArgument

private def arguments (procedure : SourceProcedure) (actuals : Array (TSyntax `statementJitArgument)) :
    TermElabM Arguments := do
  let mut result := []
  let mut atKeyword := Bool.false
  for a in actuals do
    let (formal,value) ← match a with
      | `(statementJitArgument| $name:ident = $value:tritonExpr) => do
        atKeyword := Bool.true
        pure (name.getId.eraseMacroScopes,value)
      | `(statementJitArgument| $yes:tritonExpr if $condition:tritonExpr else $no:tritonExpr) => do
        if atKeyword then throwErrorAt a "positional procedure argument follows a keyword"
        let some name := procedure.parameters[result.length]? | throwErrorAt a "too many procedure arguments"
        pure (name.toName,← `(tritonExpr| ($yes if $condition else $no)))
      | `(statementJitArgument| $value:tritonExpr) => do
        if atKeyword then throwErrorAt a "positional procedure argument follows a keyword"
        let some name := procedure.parameters[result.length]? | throwErrorAt a "too many procedure arguments"
        pure (name.toName,value)
      | _ => throwErrorAt a "expected a positional or keyword procedure argument"
    unless procedure.parameters.contains formal.toString && !(result.any (·.1 == formal)) do
      throwErrorAt a "unknown or repeated procedure argument {formal}"
    result := result ++ [(formal,value)]
  unless result.length == procedure.parameters.length do throwError "missing required procedure argument"
  return result

private partial def identifiers (s : Syntax) : List Name :=
  if s.isIdent then [s.getId.eraseMacroScopes] else s.getArgs.toList.flatMap identifiers

private partial def substitute (mapping : List (Name × Syntax)) (s : Syntax) : Syntax :=
  if s.isIdent then (mapping.lookup s.getId.eraseMacroScopes).getD s
  else s.setArgs (s.getArgs.map (substitute mapping))

private def stable (v : Value) : Bool :=
  match v with
  | `(tritonExpr| $_:ident) | `(tritonExpr| $_:num) => Bool.true
  | _ => Bool.false

private def identifier (v : Value) : Bool :=
  match v with
  | `(tritonExpr| $_:ident) => Bool.true
  | _ => Bool.false

private def conditional (v : Value) : Option (Value × Value × Value) :=
  match v with
  | `(tritonExpr| ($yes:tritonExpr if $c:tritonExpr else $no:tritonExpr)) => some (c,yes,no)
  | _ => none

private def emit (body : Array Statement) (args : Arguments) (renames : List (Name × Syntax)) :
    Array Statement :=
  let mapping := args.map (fun (k,v) => (k,v.raw)) ++ renames
  body.map (fun s => ⟨substitute mapping s.raw⟩)

private def expandCall (name : Ident) (actuals : Array (TSyntax `statementJitArgument))
    (used constants : List Name) (serial : Nat) : TermElabM (Array Statement × Nat) := do
  let some (proc,locals) := binding name.getId.eraseMacroScopes
    | throwErrorAt name "unknown sequential source procedure {name}"
  let args ← arguments proc actuals
  let body ← parseBody proc.source
  let fresh := fun (i : Nat) (n : Name) => Name.mkSimple s!"vtproc_{i}_{n}"
  let some i := (List.range (used.length+1)).map (·+serial) |>.find?
      (fun i => locals.all (fun n => !used.contains (fresh i n)))
    | throwError "cannot reserve procedure-local register names"
  let renames := locals.map fun n => (n,(mkIdent (fresh i n)).raw)
  -- The pin has one dynamic conditional output pointer. Branch at the callsite
  -- so the predicate is evaluated once, and only the selected body runs.
  let mut destination : Option (Name × Value × Value × Value) := none
  for (formal,v) in args do
    if proc.constexpr.contains formal.toString then
      let valid := match v with
        | `(tritonExpr| $n:ident) => constants.contains n.getId.eraseMacroScopes
        | `(tritonExpr| $_:num) => Bool.true
        | _ => Bool.false
      unless valid do throwErrorAt v "{formal} requires a literal or caller constexpr"
    if ["src_ptr","dst_ptr","lhs_ptr","rhs_ptr","out_ptr","ptr_x","ptr_y"].contains formal.toString &&
        stable v && !identifier v then
      throwErrorAt v "{formal} requires a pointer name"
    if !stable v then
      let some (c,yes,no) := conditional v | throwErrorAt v "expected a stable procedure argument"
      unless formal == `out_ptr && identifier yes && identifier no do
        throwErrorAt v "conditional procedure argument requires two stable output pointers"
      destination := some (formal,c,yes,no)
  if let some (formal,c,yes,no) := destination then
    let branch := fun v => emit body ((formal,v)::args) renames
    let left := branch yes
    let right := branch no
    return (#[← `(tritonStmt| if $c { $left* } else { $right* })], i+1)
  return (emit body args renames, i+1)

/-- Only complete statement calls expand. Their position inside a branch or loop is preserved. -/
private partial def expand (raw : Syntax) (used constants : List Name) :
    StateT Nat TermElabM (Array Syntax) := do
  let s : Statement := ⟨raw⟩
  if let `(tritonStmt| $name:ident($actuals:statementJitArgument,*)) := s then
    if name.getId.getPrefix.isAnonymous then
      let (result,next) ← expandCall name actuals.getElems used constants (← get)
      set next
      return result.map (·.raw)
  if raw.getKind == choiceKind then return ← expand raw[0]! used constants
  let mut children := #[]
  for child in raw.getArgs do children := children ++ (← expand child used constants)
  return #[raw.setArgs children]

scoped syntax (name := withProcedures) "with_triton_call " term " call_args "
  "[" tritonCallBinding,* "]" " dist_procedures " "in " "triton " RawSourceText.body : term

@[term_elab withProcedures] def elaborate : TermElab := fun stx expected => do
  let signature : Term := ⟨stx[1]⟩
  let args : Array (TSyntax `tritonCallBinding) := stx[4].getSepArgs.map (fun a => ⟨a⟩)
  let body ← parseBody stx.getArgs.back!.getAtomVal
  let (constants,abi) ← SourceHelpers.signatureNames signature
  let used := (body.toList.flatMap (fun s => identifiers s.raw)) ++ identifiers stx ++ abi
  let (expanded,_) ← (expand (mkNullNode (body.map (·.raw))) used constants).run 0
  let source := String.intercalate "\n" (expanded[0]!.getArgs.toList.map PythonFullConstructors.render)
  let base ← `(with_triton_call $signature call_args [$args,*] in triton {})
  let raw := Syntax.atom .none ("{\n" ++ source ++ "\n}")
  elabTerm (base.raw.setArgs (base.raw.getArgs.set! (base.raw.getNumArgs-1) raw)) expected

end VeriTile.Dist.Frontend.TritonExt.ProcedureHelpers
