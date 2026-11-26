import VeriTile.Dist.Frontend.TritonDist.DL

namespace VeriTile.Tests.TritonDistSyntax
open Lean Elab Command
open VeriTile.Triton

private def forms : List (String × String) := [
  ("x = dl.consume_token(p, v)", "#79"),
  ("x = dl.num_ranks()", "#79"),
  ("x = dl.rank()", "#79"),
  ("x = dl.symm_at(p, v)", "#79"),
  ("x = dl.wait(p, v, \"gpu\", \"acquire\")", "#79"),
  ("x = dl.wait(p, v, scope=\"gpu\", semantic=\"acquire\", waitValue=v)", "#79"),
  ("x = dl.wait(p, v, \"gpu\", \"acquire\", waitValue=v)", "#79"),
  ("dl.notify(p, v, signal=v, sig_op=\"set\", comm_scope=\"gpu\")", "#79"),
  ("dl.notify(p, v, signal=v, comm_scope=\"gpu\")", "#79"),
  ("with dl.simt_exec_region() as (lane, size) { x = lane }", "#79"),
  ("libshmem_device.barrier_all_block()", "#80"),
  ("libshmem_device.fence()", "#80"),
  ("libshmem_device.getmem_block(p, v, n, q)", "#80"),
  ("libshmem_device.getmem_nbi_block(p, v, n, q)", "#80"),
  ("libshmem_device.putmem_block(p, v, n, q)", "#80"),
  ("libshmem_device.putmem_nbi_block(p, v, n, q)", "#80"),
  ("libshmem_device.putmem_signal_block(p, v, n, q, z, op, r)", "#80"),
  ("libshmem_device.putmem_signal_nbi_block(p, v, n, q, z, op, r)", "#80"),
  ("libshmem_device.putmem_signal_nbi_warp(p, v, n, q, z, op, r)", "#80"),
  ("libshmem_device.signal_op(p, v, n, q)", "#80"),
  ("libshmem_device.signal_wait_until(p, v, n)", "#80"),
  ("x = __shfl_sync_i32(p, v, n)", "#81"),
  ("x = __shfl_up_sync_i32(p, v, n)", "#81"),
  ("x = atomic_add(p, v, semantic=\"release\", scope=\"gpu\")", "#81"),
  ("x = atomic_add(p, v, scope=\"gpu\", semantic=\"release\")", "#81"),
  ("x = atomic_cas(p, v, n, q, z)", "#81"),
  ("x = laneid()", "#81"),
  ("x = ld(p)", "#81"),
  ("x = ld(p, scope=\"gpu\", semantic=\"acquire\")", "#81"),
  ("x = ld_acquire(p, v)", "#81"),
  ("x = tid(p)", "#81"),
  ("x = tid(axis=v)", "#81"),
  ("x = tl.atomic_add(p, v, mask=v, sem=\"release\", scope=\"gpu\")", "#81"),
  ("x = tl.atomic_add(p, v, sem=\"release\", scope=\"gpu\")", "#81"),
  ("__syncthreads()", "#81"),
  ("atomic_add(p, v, semantic=\"release\", scope=\"gpu\")", "#81"),
  ("atomic_add(p, v, scope=\"gpu\", semantic=\"release\")", "#81"),
  ("membar(scope=\"gpu\")", "#81"),
  ("st(p, v)", "#81"),
  ("st(p, v, scope=\"gpu\", semantic=\"release\")", "#81"),
  ("st(p, v, semantic=\"release\", scope=\"gpu\")", "#81"),
  ("tl.atomic_add(p, v, mask=v, sem=\"release\", scope=\"gpu\")", "#81"),
  ("tl.atomic_add(p, v, sem=\"release\", scope=\"gpu\")", "#81"),
  ("barrier_all_intra_node_atomic_cas_block(p, v, n, q)", "#82"),
  ("barrier_on_this_grid(p, v)", "#82"),
  ("barrier_on_this_grid(p, use_cooperative=v)", "#82"),
  ("x = Profiler.create(profiler_buffer=v, group_id=v, num_groups=v, is_leader=v, ENABLE_PROFILING=v)", "#452"),
  ("profiler.record(is_start=v, task_type=v)", "#452")]

private def parseBlock (env : Environment) (s : String) :=
  Parser.runParserCategory env `term ("triton { " ++ s ++ " }")

private def hasDistNode (stx : Syntax) : Bool :=
  (stx.find? fun n => (`VeriTile.Dist.Frontend.TritonDist).isPrefixOf n.getKind).isSome

private def diagnosticOf (stx : Syntax) : CommandElabM String := liftTermElabM do
  try
    discard <| Term.withoutErrToSorry (Term.elabTermAndSynthesize stx none)
    return ""
  catch e => return ← e.toMessageData.toString

-- M5 records exactly these upstream parses when the distributed scope is closed.
private def upstreamOverlap : List String := [
  "x = dl.num_ranks()", "x = dl.rank()", "x = laneid()", "x = ld(p)", "x = tid(p)",
  "tl.atomic_add(p, v, mask=v, sem=\"release\", scope=\"gpu\")",
  "tl.atomic_add(p, v, sem=\"release\", scope=\"gpu\")"]

#guard_msgs in
run_cmd
  let mut overlapping := []
  for (body, _) in forms do
    if let .ok stx := parseBlock (← getEnv) body then
      overlapping := body :: overlapping
      if hasDistNode stx then throwError "distributed syntax leaked outside scope: {body}"
      if (← diagnosticOf stx).isEmpty then throwError "unexpected upstream elaboration: {body}"
  unless overlapping.reverse == upstreamOverlap do
    throwError "unexpected set of upstream parses: {overlapping.reverse}"

open scoped VeriTile.Dist.Frontend.TritonDist

#guard_msgs in
run_cmd for (body, ticket) in forms do
  let .ok stx := parseBlock (← getEnv) body | throwError "failed to parse: {body}"
  unless hasDistNode stx do throwError "upstream fallback for distributed call: {body}"
  let diagnostic ← diagnosticOf stx
  let expected := if ticket == "#79" then "" else "not implemented: " ++ ticket
  unless diagnostic == expected do
    throwError "{body}: expected '{expected}', got '{diagnostic}'"

-- Excluded surface names from PrimitiveSources §§5.1–5.8. Exercise both statement
-- and value positions without counting a generic upstream identifier-call as a distributed form.
private def excluded : List (String × String) := [
  ("dl.", "extract insert vector make_vector zeros_vector ld_vector st_vector SMEM_GENERIC_POINTER_ADDR_SPACE SharedMemoryDesc allocate_smem smem_index smem_load smem_store smem_get_ptr get_smem_shared_address_u32 smem_dealloc tma extern_call"),
  ("dl.tma.", "create_tmap_2d tmap_update_address PipelineState TmaPipeline store_and_wait"),
  ("libshmem_device.", "set_rocshmem_ctx my_pe n_pes team_my_pe team_n_pes int_p remote_ptr remote_mc_ptr barrier_all barrier_all_vec barrier_all_warp barrier_all_wave barrier_all_wg barrier barrier_vec barrier_block barrier_warp sync_all sync_all_block sync_all_warp sync team_sync_block team_sync_warp quiet quiet_pe getmem_nbi_warp getmem_warp getmem_nbi getmem_nbi_wave getmem_nbi_wg getmem getmem_wave getmem_wg putmem_warp putmem_nbi_warp putmem putmem_wave putmem_wg putmem_nbi putmem_nbi_wave putmem_nbi_wg putmem_signal_nbi putmem_signal putmem_signal_warp putmem_signal_wave putmem_signal_wg putmem_signal_nbi_wave putmem_signal_nbi_wg uint64_wait_until_equals ulong_put_signal broadcastmem broadcastmem_warp broadcastmem_block broadcast broadcast_warp broadcast_block fcollectmem fcollectmem_warp fcollectmem_block fcollect fcollect_warp fcollect_block putmem_rma putmem_rma_block putmem_rma_warp putmem_rma_nbi putmem_rma_nbi_block putmem_rma_nbi_warp putmem_signal_rma putmem_signal_rma_nbi putmem_signal_rma_warp putmem_signal_rma_nbi_warp putmem_signal_rma_block putmem_signal_rma_nbi_block team_translate_pe"),
  ("", "ld_vector st_vector pack unpack threads_per_warp num_threads num_warps tl_type_to_ptx_suffix __fence tma_sync load_v4_u32 load_v4_b32 load_v4_s32 load_v2_b64 st_v4_u32 st_v4_b32 st_v2_u32 multimem_st_b64 multimem_st_b32 multimem_st_v2 multimem_st_v4 multimem_st_p_b32 multimem_ld_reduce_p_v4 multimem_ld_reduce_v4 ntid red_release arrive_inc arrive_inc_asm ld_b32 st_b32 atomic_add_per_warp wait_eq __shfl_sync_with_mode_i32 __shfl_down_sync_i32 __shfl_xor_sync_i32 __ballot_sync globaltimer_lo globaltimer_hi globaltimer smid fence pack_b32_v2"),
  ("T.", "fence_gpu fence_sys get_rank get_num_ranks put_warp get_warp put_block get_block ld st atom_add wait_eq wait_ne wait_ge wait_le wait_gt wait_lt init_barrier_gpu arrive_barrier_gpu wait_barrier_gpu sync_barrier_gpu barrier_blocks sync_blocks multimem_ld_reduce multimem_st multimem_red multimem_tma_store multimem_signal multimem_signal_add copy tma_copy atomic_add atomic_addx2"),
  ("T.", "set_signal wait_eq"),
  ("common_ops.", "set_signal wait_eq"),
  ("tl.extra.cuda.", "num_threads num_warps utils.num_warps")]

-- The upstream parser reports a position before its diagnostic. Match its message
-- independently of the length of the source name, and pin elaboration errors verbatim.
#guard_msgs in
run_cmd for (qualifier, names) in excluded do
  for name in names.splitOn " " do
    for args in ["", "p", "p, v", "p, v, n", "p, v, n, q"] do
      let call := qualifier ++ name ++ "(" ++ args ++ ")"
      for valuePosition in [Bool.false, Bool.true] do
        let body := if valuePosition then "result = " ++ call else call
        match parseBlock (← getEnv) body with
        | .error diagnostic =>
          let expected := if valuePosition then "expected ')'"
            else "expected '%', '*=', '+=', ',', '-=', '/=', ':=' or '='"
          unless (!valuePosition || args.contains ',') && diagnostic.endsWith (": " ++ expected) do
            throwError "{body}: unexpected parser diagnostic: {diagnostic}"
        | .ok stx =>
          if hasDistNode stx then throwError "unexpected distributed production: {body}"
          let expected := if args.isEmpty then "unexpected syntax\n  triton {" ++ body ++ "}"
            else "random source helper requires an explicit tl.source_helper binding"
          let diagnostic ← diagnosticOf stx
          unless valuePosition && (args.isEmpty || args == "p") && diagnostic == expected do
            throwError "{body}: unexpected elaborator diagnostic: {diagnostic}"

/-- error: tl.load: unknown kwarg `volatile`. Only `mask`, `other`, `dtype`, `boundary_check`, `padding_option`, and `eviction_policy` are recognized. -/
#guard_msgs in
#check (triton { tl.region p = tl.int32
  x = tl.load(p + 0, volatile=True)
} : ComputeKernel)

/-- error: random source helper requires an explicit tl.source_helper binding -/
#guard_msgs in
#check (triton { x = dl.allocate_smem(1) } : ComputeKernel)

open VeriTile.Dist
open VeriTile.Dist.Frontend.TritonDist

private def inputWord : Addr := ⟨.global 1, ⟨"signal"⟩, 9⟩
private def peerWord : Addr := ⟨.global 2, ⟨"signal"⟩, 9⟩
private def context : DL.CallContext where
  agent := .thread ⟨1, [0]⟩ 0 3
  numRanks := 4
  blockSize := 32
  symmetric := fun _ => Bool.true
  evalAddr := fun _ => some inputWord
  evalNat := fun stx =>
    match stx[0][0].getAtomVal with
    | "1" => some 1
    | "2" => some 2
    | "7" => some 7
    | "11" => some 11
    | _ => none

private def lower (source : DL.Source) : List (Option DL.Result) :=
  source.sites.map fun site => site.call.lower context

example :
    lower (triton {
      r = dl.rank()
      n = dl.num_ranks()
      peer = dl.symm_at(signal, 2)
      with dl.simt_exec_region() as (lane, size) { x = lane }
    }) = [some (.scalar 1), some (.scalar 4), some (.address peerWord),
      some (.simt `lane `size 3 32)] := rfl

example :
    lower (triton {
      dl.notify(signal, 2, signal=11, comm_scope="intra_node")
      dl.notify(signal, 2, signal=7, sig_op="add", comm_scope="gpu")
    }) = [some (.event (.bump ⟨.word peerWord, .set, 11, .atomic .sys .release⟩)),
      some (.event (.bump ⟨.word peerWord, .add, 7, .atomic .gpu .release⟩))] := rfl

private def waitModes (source : DL.Source) : List (VeriTile.Dist.Scope × MemOrder) :=
  source.sites.filterMap fun site => match site.call with
    | .wait _ _ _ scope order => some (scope, order)
    | _ => none

-- Tutorial 01's two wait sites at the TD pin, L88–96 and L126–133.
theorem tutorial01GpuWaitModes :
    waitModes (triton {
      if pid < n {
        for j in range(pid, count, stride) {
          token = dl.wait(dl.symm_at(flag, peer) + offset, 1, "gpu", "acquire", waitValue=round * 2)
          payload = dl.consume_token(payload, token)
        }
      } else {
        for j in range(pid, count, stride) {
          token = dl.wait(flag + offset, 1, "gpu", "acquire", waitValue=round * 2 + 1)
          queue = dl.consume_token(queue, token)
        }
      }
    }) = [(.gpu, .acquire), (.gpu, .acquire)] := rfl

theorem tutorial01SystemWaitModes :
    waitModes (triton {
      if pid < n {
        for j in range(pid, count, stride) {
          token = dl.wait(dl.symm_at(flag, peer) + offset, 1, "sys", "acquire", waitValue=round * 2)
          payload = dl.consume_token(payload, token)
        }
      } else {
        for j in range(pid, count, stride) {
          token = dl.wait(flag + offset, 1, "sys", "acquire", waitValue=round * 2 + 1)
          queue = dl.consume_token(queue, token)
        }
      }
    }) = [(.sys, .acquire), (.sys, .acquire)] := rfl

#print axioms tutorial01GpuWaitModes

#print axioms tutorial01SystemWaitModes

private abbrev bulkWait : DL.Wait := ⟨inputWord, 2, 1, .gpu, .acquire⟩

example :
    lower (triton { tok = dl.wait(signal, 2, "gpu", "acquire") }) =
      [some (.wait bulkWait)] := rfl

example :
    bulkWait.event .eq 0 = .wait (.word inputWord) .eq 1 (.atomic .gpu .acquire) ∧
      bulkWait.event .ge 1 =
        .wait (.word { inputWord with offset := 10 }) .ge 1 (.atomic .gpu .acquire) :=
  ⟨rfl, rfl⟩

private def reader : Agent := .rank 1

example : ¬ bulkWait.Observed reader .eq 0 [] := by
  intro ⟨_, index, _, _⟩
  exact Fin.elim0 (index 0)

private abbrev observations (reading : DL.WaitReading) : Trace :=
  [(reader, bulkWait.event reading 1), (reader, bulkWait.event reading 0)]

private theorem allObserved (reading : DL.WaitReading) :
    bulkWait.Observed reader reading 0 (observations reading) := by
  refine ⟨Nat.zero_le _, Fin.rev, fun _ _ equal => Fin.rev_inj.mp equal, ?_⟩
  intro i
  refine ⟨Nat.zero_le _, ?_⟩
  refine Fin.cases rfl (fun j => ?_) i
  have equal : j = 0 := Subsingleton.elim _ _
  subst j
  rfl

example : ¬ bulkWait.Observed reader .eq 2 (observations .eq) := by
  intro ⟨_, index, _, observed⟩
  exact Nat.not_le_of_gt (index 0).isLt (observed 0).1

example (reading : DL.WaitReading) :
    DL.consumeToken inputWord ⟨allObserved reading⟩ = inputWord := rfl

example : match lower (triton { ready = dl.consume_token(value, token) }) with
    | [some (.afterWait value token)] => value[0].getId = `value ∧ token[0].getId = `token
    | _ => False := ⟨rfl, rfl⟩

/-- error: dl.wait: unsupported scope 'cluster' -/
#guard_msgs in
#check (triton { token = dl.wait(signal, 2, "cluster", "acquire") } : DL.Source)

end VeriTile.Tests.TritonDistSyntax
