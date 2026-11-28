import VeriTile.Triton.DSL.Expansion

/-! Unsigned A2.1 surface for the spellings reached at Triton-distributed 7908e4ea.
See documents/dist/TritonDistSubset.md for the event and evidence attached to each call.
The scoped productions use non-reserved identifiers so importing this module does not
reserve a user identifier. No distributed operation has executable semantics here. -/

namespace VeriTile.Dist.Frontend.TritonDist
open Lean Elab Term
open VeriTile.Triton.DSL

declare_syntax_cat distributedCallExpr
scoped syntax lookahead(ident) &"dl.consume_token" "(" tritonExpr "," tritonExpr ")" : distributedCallExpr
scoped syntax lookahead(ident) &"dl.num_ranks" "(" ")" : distributedCallExpr
scoped syntax lookahead(ident) &"dl.rank" "(" ")" : distributedCallExpr
scoped syntax lookahead(ident) &"dl.symm_at" "(" tritonExpr "," tritonExpr ")" : distributedCallExpr
scoped syntax lookahead(ident) &"dl.wait" "(" tritonExpr "," tritonExpr "," tritonExpr "," tritonExpr ")" : distributedCallExpr
scoped syntax lookahead(ident) &"dl.wait" "(" tritonExpr "," tritonExpr "," &"scope" "=" tritonExpr "," &"semantic" "=" tritonExpr "," &"waitValue" "=" tritonExpr ")" : distributedCallExpr
scoped syntax lookahead(ident) &"dl.wait" "(" tritonExpr "," tritonExpr "," tritonExpr "," tritonExpr "," &"waitValue" "=" tritonExpr ")" : distributedCallExpr
scoped syntax (name := dlExpr) (priority := high) distributedCallExpr : tritonExpr

declare_syntax_cat distributedCallStmt
scoped syntax lookahead(ident) &"dl.notify" "(" tritonExpr "," tritonExpr "," &"signal" "=" tritonExpr "," &"sig_op" "=" tritonExpr "," &"comm_scope" "=" tritonExpr ")" : distributedCallStmt
scoped syntax lookahead(ident) &"dl.notify" "(" tritonExpr "," tritonExpr "," &"signal" "=" tritonExpr "," &"comm_scope" "=" tritonExpr ")" : distributedCallStmt
scoped syntax "with" lookahead(ident) &"dl.simt_exec_region" "(" ")" "as" "(" ident "," ident ")" "{" tritonStmt* "}" : distributedCallStmt
scoped syntax (name := dlStmt) (priority := high) distributedCallStmt : tritonStmt

declare_syntax_cat shmemPtr
scoped syntax tritonExpr : shmemPtr
-- The tutorial 03 byte view is an operand of a memory transfer.
scoped syntax (name := shmemByteView) (priority := high)
  "tl.cast(" tritonExpr "," "tl.pointer_type(" "tl.int8" ")" ")" ("+" tritonExpr)? : shmemPtr

declare_syntax_cat shmemCallStmt
scoped syntax lookahead(ident) &"libshmem_device.barrier_all_block" "(" ")" : shmemCallStmt
scoped syntax lookahead(ident) &"libshmem_device.fence" "(" ")" : shmemCallStmt
scoped syntax lookahead(ident) &"libshmem_device.getmem_block" "(" shmemPtr "," shmemPtr "," tritonExpr "," tritonExpr ")" : shmemCallStmt
scoped syntax lookahead(ident) &"libshmem_device.getmem_nbi_block" "(" shmemPtr "," shmemPtr "," tritonExpr "," tritonExpr ")" : shmemCallStmt
scoped syntax lookahead(ident) &"libshmem_device.putmem_block" "(" shmemPtr "," shmemPtr "," tritonExpr "," tritonExpr ")" : shmemCallStmt
scoped syntax lookahead(ident) &"libshmem_device.putmem_nbi_block" "(" shmemPtr "," shmemPtr "," tritonExpr "," tritonExpr ")" : shmemCallStmt
scoped syntax lookahead(ident) &"libshmem_device.putmem_signal_block" "(" shmemPtr "," shmemPtr "," tritonExpr "," tritonExpr "," tritonExpr "," tritonExpr "," tritonExpr ")" : shmemCallStmt
scoped syntax lookahead(ident) &"libshmem_device.putmem_signal_nbi_block" "(" shmemPtr "," shmemPtr "," tritonExpr "," tritonExpr "," tritonExpr "," tritonExpr "," tritonExpr ")" : shmemCallStmt
scoped syntax lookahead(ident) &"libshmem_device.putmem_signal_nbi_warp" "(" shmemPtr "," shmemPtr "," tritonExpr "," tritonExpr "," tritonExpr "," tritonExpr "," tritonExpr ")" : shmemCallStmt
scoped syntax lookahead(ident) &"libshmem_device.signal_op" "(" tritonExpr "," tritonExpr "," tritonExpr "," tritonExpr ")" : shmemCallStmt
scoped syntax lookahead(ident) &"libshmem_device.signal_wait_until" "(" tritonExpr "," tritonExpr "," tritonExpr ")" : shmemCallStmt
scoped syntax (name := pendingShmemStmt) (priority := high) shmemCallStmt : tritonStmt

declare_syntax_cat extraCallExpr
scoped syntax lookahead(ident) &"__shfl_sync_i32" "(" tritonExpr "," tritonExpr "," tritonExpr ")" : extraCallExpr
scoped syntax lookahead(ident) &"__shfl_up_sync_i32" "(" tritonExpr "," tritonExpr "," tritonExpr ")" : extraCallExpr
scoped syntax lookahead(ident) &"atomic_add" "(" tritonExpr "," tritonExpr "," &"semantic" "=" tritonExpr "," &"scope" "=" tritonExpr ")" : extraCallExpr
scoped syntax lookahead(ident) &"atomic_add" "(" tritonExpr "," tritonExpr "," &"scope" "=" tritonExpr "," &"semantic" "=" tritonExpr ")" : extraCallExpr
scoped syntax lookahead(ident) &"atomic_cas" "(" tritonExpr "," tritonExpr "," tritonExpr "," tritonExpr "," tritonExpr ")" : extraCallExpr
scoped syntax lookahead(ident) &"laneid" "(" ")" : extraCallExpr
scoped syntax lookahead(ident) &"ld" "(" tritonExpr ")" : extraCallExpr
scoped syntax lookahead(ident) &"ld" "(" tritonExpr "," &"scope" "=" tritonExpr "," &"semantic" "=" tritonExpr ")" : extraCallExpr
scoped syntax lookahead(ident) &"ld_acquire" "(" tritonExpr "," tritonExpr ")" : extraCallExpr
scoped syntax lookahead(ident) &"tid" "(" tritonExpr ")" : extraCallExpr
scoped syntax lookahead(ident) &"tid" "(" &"axis" "=" tritonExpr ")" : extraCallExpr
scoped syntax "tl.atomic_add(" tritonExpr "," tritonExpr "," &"mask" "=" tritonExpr "," &"sem" "=" tritonExpr "," &"scope" "=" tritonExpr ")" : extraCallExpr
scoped syntax "tl.atomic_add(" tritonExpr "," tritonExpr "," &"sem" "=" tritonExpr "," &"scope" "=" tritonExpr ")" : extraCallExpr
scoped syntax (name := pendingExtraExpr) (priority := high) extraCallExpr : tritonExpr

declare_syntax_cat extraCallStmt
scoped syntax lookahead(ident) &"__syncthreads" "(" ")" : extraCallStmt
scoped syntax lookahead(ident) &"atomic_add" "(" tritonExpr "," tritonExpr "," &"semantic" "=" tritonExpr "," &"scope" "=" tritonExpr ")" : extraCallStmt
scoped syntax lookahead(ident) &"atomic_add" "(" tritonExpr "," tritonExpr "," &"scope" "=" tritonExpr "," &"semantic" "=" tritonExpr ")" : extraCallStmt
scoped syntax lookahead(ident) &"membar" "(" &"scope" "=" tritonExpr ")" : extraCallStmt
scoped syntax lookahead(ident) &"st" "(" tritonExpr "," tritonExpr ")" : extraCallStmt
scoped syntax lookahead(ident) &"st" "(" tritonExpr "," tritonExpr "," &"scope" "=" tritonExpr "," &"semantic" "=" tritonExpr ")" : extraCallStmt
scoped syntax lookahead(ident) &"st" "(" tritonExpr "," tritonExpr "," &"semantic" "=" tritonExpr "," &"scope" "=" tritonExpr ")" : extraCallStmt
scoped syntax "tl.atomic_add(" tritonExpr "," tritonExpr "," &"mask" "=" tritonExpr "," &"sem" "=" tritonExpr "," &"scope" "=" tritonExpr ")" : extraCallStmt
scoped syntax "tl.atomic_add(" tritonExpr "," tritonExpr "," &"sem" "=" tritonExpr "," &"scope" "=" tritonExpr ")" : extraCallStmt
scoped syntax (name := pendingExtraStmt) (priority := high) extraCallStmt : tritonStmt

-- An empty polling loop is lowered by the A3 call frontend.
scoped syntax (name := extraSpinStmt) (priority := high)
  "while" tritonExpr "{" (&"pass")? "}" : tritonStmt

declare_syntax_cat commonCallStmt
scoped syntax lookahead(ident) &"barrier_all_intra_node_atomic_cas_block" "(" tritonExpr "," tritonExpr "," tritonExpr "," tritonExpr ")" : commonCallStmt
scoped syntax lookahead(ident) &"barrier_on_this_grid" "(" tritonExpr "," tritonExpr ")" : commonCallStmt
scoped syntax lookahead(ident) &"barrier_on_this_grid" "(" tritonExpr "," &"use_cooperative" "=" tritonExpr ")" : commonCallStmt
scoped syntax (name := pendingCommonStmt) (priority := high) commonCallStmt : tritonStmt

declare_syntax_cat profilerCallExpr
scoped syntax lookahead(ident) &"Profiler.create" "(" &"profiler_buffer" "=" tritonExpr "," &"group_id" "=" tritonExpr "," &"num_groups" "=" tritonExpr "," &"is_leader" "=" tritonExpr "," &"ENABLE_PROFILING" "=" tritonExpr ")" : profilerCallExpr
scoped syntax (name := pendingProfilerExpr) (priority := high) profilerCallExpr : tritonExpr

declare_syntax_cat profilerCallStmt
scoped syntax lookahead(ident) &"profiler.record" "(" &"is_start" "=" tritonExpr "," &"task_type" "=" tritonExpr ")" : profilerCallStmt
scoped syntax (name := pendingProfilerStmt) (priority := high) profilerCallStmt : tritonStmt

-- `lookahead(ident)` dispatches non-reserved primitive names in a Pratt category
-- without registering them as global tokens. The existing `tl.atomic_add(` token is reused.
inductive Family where
  | dl | shmem | extra
  deriving DecidableEq

def family? (kind : Name) : Option Family :=
  match kind with
  | ``dlExpr | ``dlStmt => some .dl
  | ``pendingShmemStmt => some .shmem
  | ``pendingExtraExpr | ``pendingExtraStmt | ``extraSpinStmt => some .extra
  | _ => none

def checkPendingCalls (stx : Syntax) : TermElabM Unit := do
  if let some call := stx.find? (fun s =>
      [``pendingCommonStmt, ``pendingProfilerExpr, ``pendingProfilerStmt].contains s.getKind) then
    let ticket := if call.isOfKind ``pendingCommonStmt then "#82" else "#452"
    throwErrorAt call "not implemented: {ticket}"

/-- An explicit family-specific result still requests that family's source view.
An inferred result uses that view when only the family module is imported. -/
def checkFamilySource (stx : Syntax) (expected : Option Expr)
    (sourceType : Name) (family : Family) : TermElabM Unit := do
  if let some type := expected then
    unless (← Meta.whnf type).isConstOf sourceType do throwUnsupportedSyntax
  else if (← getEnv).contains `VeriTile.Dist.Frontend.TritonDist.Body then
    throwUnsupportedSyntax
  unless (stx.find? (fun s => family? s.getKind == some family)).isSome do
    throwUnsupportedSyntax
  checkPendingCalls stx
  if let some call := stx.find? (fun s =>
      match family? s.getKind with
      | some other => other != family
      | none => Bool.false) then
    throwErrorAt call "use TritonDist.Body for a block with several distributed call families"

@[scoped term_elab VeriTile.Triton.DSL.tritonBlock]
def pending : TermElab := fun stx _ => do
  checkPendingCalls stx
  if (← getEnv).contains `VeriTile.Dist.Frontend.TritonDist.Body then throwUnsupportedSyntax
  let env ← getEnv
  if let some call := stx.find? (fun s =>
      match family? s.getKind with
      | some .shmem => !env.contains `VeriTile.Dist.Frontend.TritonDist.Shmem.Source
      | some .extra => !env.contains `VeriTile.Dist.Frontend.TritonDist.LanguageExtra.Source
      | _ => Bool.false) then
    throwErrorAt call "import TritonDist.Segments or the corresponding family frontend"
  throwUnsupportedSyntax

partial def quoteDistSyntax (stx : Syntax) : TermElabM (TSyntax `term) := do
  match stx with
  | .missing => `(Syntax.missing)
  | .atom _ token =>
    let token := quote token
    `(Syntax.atom SourceInfo.none $token)
  | .ident _ spelling name _ =>
    let spelling := quote spelling.toString
    let name := quote name.eraseMacroScopes
    `(Syntax.ident SourceInfo.none (String.toRawSubstring $spelling) $name [])
  | .node _ kind args =>
    let args ← args.mapM quoteDistSyntax
    let kind := quote kind
    `(Syntax.node SourceInfo.none $kind #[$args,*])

inductive OperandKind where
  | value | nat | address | token
  deriving DecidableEq

/-- The composed frontend can bind operands to registers at the same points
where the family source views quote them. -/
abbrev QuoteOperand := OperandKind → Syntax → TermElabM (TSyntax `term)

def quoteSourceOperand : QuoteOperand := fun _ => quoteDistSyntax

-- Volatile loads are explicitly outside the signed A2.1 source subset.
private def checkDistVolatileLoads (stx : Syntax) : TermElabM Unit := do
  let hasVolatile (raw : Syntax) := match (⟨raw⟩ : TSyntax `tritonMemKwarg) with
    | `(tritonMemKwarg| $name:ident = $_:tritonExpr)
    | `(tritonMemKwarg| $name:ident = $_:tritonDType) => name.getId.eraseMacroScopes == `volatile
    | _ => Bool.false
  if let some load := stx.find? (fun raw =>
      raw.getArgs.any (fun arg => arg.isAtom && arg.getAtomVal == "tl.load(") &&
        (raw.find? hasVolatile).isSome) then
    let message := "tl.load: unknown kwarg `volatile`. Only `mask`, `other`, `dtype`, " ++
      "`boundary_check`, `padding_option`, and `eviction_policy` are recognized."
    throwErrorAt load message

-- These are the same source-helper passes used by the ordinary Triton block.
-- Run them for validation only and retain the original syntax and tree paths.
def checkDistSourceCalls (stx : Syntax) : TermElabM Unit := do
  let `(triton { $stmts:tritonStmt* }) := stx | throwUnsupportedSyntax
  let checked ← liftMacroM do
    let normalized ← stmts.toList.mapM fun stmt =>
      return (⟨← Inference.normalizeControlFlow stmt.raw⟩ : TSyntax `tritonStmt)
    RandomProfile.prepare (← FiniteHelperSource.prepare normalized)
  -- The dotted zero-argument parser also admits excluded names. The finite
  -- helper pass consumes the supported dtype predicate in its declaration.
  if checked.any fun stmt =>
      (stmt.raw.find? (·.isOfKind ``tritonSourceIsFP64Dotted)).isSome then
    throwErrorAt stx "unexpected syntax{indentD stx}"
  checkDistVolatileLoads stx

end VeriTile.Dist.Frontend.TritonDist
