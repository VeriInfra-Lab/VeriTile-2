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
scoped syntax (name := pendingDistributedExpr) (priority := high) distributedCallExpr : tritonExpr

declare_syntax_cat distributedCallStmt
scoped syntax lookahead(ident) &"dl.notify" "(" tritonExpr "," tritonExpr "," &"signal" "=" tritonExpr "," &"sig_op" "=" tritonExpr "," &"comm_scope" "=" tritonExpr ")" : distributedCallStmt
scoped syntax lookahead(ident) &"dl.notify" "(" tritonExpr "," tritonExpr "," &"signal" "=" tritonExpr "," &"comm_scope" "=" tritonExpr ")" : distributedCallStmt
scoped syntax "with" lookahead(ident) &"dl.simt_exec_region" "(" ")" "as" "(" ident "," ident ")" "{" tritonStmt* "}" : distributedCallStmt
scoped syntax (name := pendingDistributedStmt) (priority := high) distributedCallStmt : tritonStmt

declare_syntax_cat shmemCallStmt
scoped syntax lookahead(ident) &"libshmem_device.barrier_all_block" "(" ")" : shmemCallStmt
scoped syntax lookahead(ident) &"libshmem_device.fence" "(" ")" : shmemCallStmt
scoped syntax lookahead(ident) &"libshmem_device.getmem_block" "(" tritonExpr "," tritonExpr "," tritonExpr "," tritonExpr ")" : shmemCallStmt
scoped syntax lookahead(ident) &"libshmem_device.getmem_nbi_block" "(" tritonExpr "," tritonExpr "," tritonExpr "," tritonExpr ")" : shmemCallStmt
scoped syntax lookahead(ident) &"libshmem_device.putmem_block" "(" tritonExpr "," tritonExpr "," tritonExpr "," tritonExpr ")" : shmemCallStmt
scoped syntax lookahead(ident) &"libshmem_device.putmem_nbi_block" "(" tritonExpr "," tritonExpr "," tritonExpr "," tritonExpr ")" : shmemCallStmt
scoped syntax lookahead(ident) &"libshmem_device.putmem_signal_block" "(" tritonExpr "," tritonExpr "," tritonExpr "," tritonExpr "," tritonExpr "," tritonExpr "," tritonExpr ")" : shmemCallStmt
scoped syntax lookahead(ident) &"libshmem_device.putmem_signal_nbi_block" "(" tritonExpr "," tritonExpr "," tritonExpr "," tritonExpr "," tritonExpr "," tritonExpr "," tritonExpr ")" : shmemCallStmt
scoped syntax lookahead(ident) &"libshmem_device.putmem_signal_nbi_warp" "(" tritonExpr "," tritonExpr "," tritonExpr "," tritonExpr "," tritonExpr "," tritonExpr "," tritonExpr ")" : shmemCallStmt
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
private def owner? (k : Name) : Option String :=
  match k with
  | ``pendingDistributedExpr | ``pendingDistributedStmt => some "#79"
  | ``pendingShmemStmt => some "#80"
  | ``pendingExtraExpr | ``pendingExtraStmt => some "#81"
  | ``pendingCommonStmt => some "#82"
  | ``pendingProfilerExpr | ``pendingProfilerStmt => some "#452"
  | _ => none

@[scoped term_elab VeriTile.Triton.DSL.tritonBlock]
def pending : TermElab := fun stx _ => do
  let some call := stx.find? fun s => (owner? s.getKind).isSome | throwUnsupportedSyntax
  throwErrorAt call "not implemented: {(owner? call.getKind).get!}"

end VeriTile.Dist.Frontend.TritonDist
