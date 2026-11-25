# Triton-distributed surface and event mapping

A2.1 mapping for tutorials 01–08 and the Triton-distributed K-M kernels at `7908e4ea9010bb2238f9f05b28c904fd4b71c60a`. Open `VeriTile.Dist.Frontend.TritonDist` after importing its `Syntax` module. A recognized distributed form reports its implementation ticket when elaborated. The coordinator recorded the user’s signature on M1–M5 and M7 on 2026-11-24. The user decided M6 on 2026-11-24. [M6 decision](https://github.com/VeriInfra-Lab/VeriTile-2/issues/78#issuecomment-7144445807) · [Signed rows on #78](https://github.com/VeriInfra-Lab/VeriTile-2/issues/78#issuecomment-7121319432)

## Target calls

The source inventory uses 51 distinct roots from the generated Triton-distributed kernel index: every K-M row, the fourteen tutorial functions, and the seven common/reduce-scatter functions reached by the tutorials. Tutorial 04 belongs to both families and counts once. A root uses a primitive if it calls it directly or through a kernel-side helper. Host launches identify roots but do not charge all the primitive uses of the launched kernel to its caller. K-M’s additional host-launched `threadblock_swizzle_ag_moe_kernel` is inventoried separately in the MoE report (it uses the already listed `tid`, `__syncthreads`, `tl.atomic_add` and `next_power_of_2`). The counts exclude that extra root. Imported `warp_prefix_sum_kernel` is followed from every caller. The A9 wrapper counts as a call at its registered cooperative boundary. [Generated census](../census/MinimalSyntax.md#triton-distributed-kernels) · [Tutorial reachability, §2](EventControlFlow.md#2-sources) · [MoE census and imported functions](MoEInventory.md)

Each registry key uses its section of [PrimitiveSources](PrimitiveSources.md#5-tables): `dl` §5.1, `shmem` §5.3, `extra` §5.4, `tl.atomic_add` §5.7, `common` §5.8. The surface column gives the source spellings, including unqualified imports. Each row cites the evidence or rule IDs in that registry; the profiler decision is separate. The semantics column uses the [signed event types](../../VeriTile/Dist/Event.lean) and [counter lemmas](../../VeriTile/Dist/Event/Counter.lean). Expression arguments and literal byte counts are evaluated by the calling program. A counter names an address, a CTA phase, a rendezvous, or the deliveries of an issuing agent.

| Registry key | Observed surface | Event or local result | Evidence / treatment | Roots | Implementation |
| --- | --- | --- | --- | ---: | --- |
| `.record` | `profiler.record(is_start=…, task_type=…)` | Identity when profiling is off; refuse an enabled profiler. | Decision #452 | 3 | #452 |
| `Profiler.create` | `Profiler.create(profiler_buffer=…, group_id=…, num_groups=…, is_leader=…, ENABLE_PROFILING=…)` | Construct disabled profiler state when profiling is off. Active profiling is outside the subset. | Decision #452 | 3 | #452 |
| `common.barrier_all_intra_node_atomic_cas_block` | `barrier_all_intra_node_atomic_cas_block(localRank, rank, localSize, flags)` | Inline the two CAS spins and the block barrier; each uses its own event row. | W4; A1(b), A3, A8, D8 | 6 | #82 |
| `common.barrier_on_this_grid` | `barrier_on_this_grid(p, use_cooperative=…)`<br>`barrier_on_this_grid(p, cooperative)` | Under a cooperative launch: grid-wide arrival and wait with ordering. Use one rendezvous per grid launch, with successive counter thresholds (M2). Otherwise W4. | A9; W4 outside premise | 6 | #82 |
| `common.next_power_of_2` | `next_power_of_2(n)` | No event. The registered W3 reading leaves the value unspecified. The existing constexpr extension separately specializes its pinned body. | W3, §5.8 | 2 | #449 |
| `dl.consume_token` | `dl.consume_token(value, token)` | No event; use the value after its wait token in the same agent. | E-TD2, E-TD4 | 6 | #79 |
| `dl.notify` | `dl.notify(p, rank, signal=…, comm_scope=…)`<br>`dl.notify(p, rank, signal=…, sig_op=…, comm_scope=…)` | Remote word bump, set (default) or add, release; `intra_node` → atomic sys, `gpu` → atomic gpu. | A2; A8 where cross-GPU | 2 | #79 |
| `dl.num_ranks` | `dl.num_ranks()` | No event; number of participating ranks. | E-TD6 | 7 | #79 |
| `dl.rank` | `dl.rank()` | No event; caller rank. | E-TD6 | 7 | #79 |
| `dl.simt_exec_region` | `with dl.simt_exec_region() as (thread, size)` | No event on entry; bind the thread index and block size for the enclosed SIMT program. | E-TD9 | 9 | #79 |
| `dl.symm_at` | `dl.symm_at(p, rank)` | No event; symmetric address on the designated rank. Later accesses keep their own mode. | E-TD5 | 12 | #79 |
| `dl.wait` | `dl.wait(p, count, scope=…, semantic=…, waitValue=…)`<br>`dl.wait(p, count, scope, semantic)`<br>`dl.wait(p, count, scope, semantic, waitValue=…)` | Each addressed word has its own wait step in mode `atomic scope order`; prove both eq and ge. The returned token follows every observation. M3 leaves their order and interleaving unspecified. | E-TD1–3, D5, D6; A1(a) | 6 | #79 |
| `extra.__shfl_sync_i32` | `__shfl_sync_i32(mask, value, lane)` | The helper body reaches the W3 shuffle implementation. Return an unspecified value, with no event or visibility edge. | W4 → W3, M7 | 5 | #81 |
| `extra.__shfl_up_sync_i32` | `__shfl_up_sync_i32(mask, value, delta)` | The imported warp prefix sum reaches the same W3 shuffle implementation via W4. Its value is unspecified. | W4 → W3, M7 | 5 | #81 |
| `extra.__syncthreads` | `__syncthreads()` | Phase counter of this CTA; each participant arrives and waits, ordering accesses across the phase. | E-TD8, E-CU7, D8 | 20 | #81 |
| `extra.atomic_add` | `atomic_add(p, value, scope=…, semantic=…)`<br>`atomic_add(p, value, semantic=…, scope=…)` | Per element: access update, atomic scope/order; return old value even when the caller discards it. | D5; A1(a,b) | 5 | #81 |
| `extra.atomic_cas` | `atomic_cas(p, old, new, scope, semantic)` | Strong compare-exchange returning the observed value. For the empty-body spin, wait and successful set on the same word in one step; retain the source scope/order. | D5; A1(a,b), A3, A8 | 7 | #81 |
| `extra.laneid` | `laneid()` | No event; unspecified value. | W3 | 5 | #81 |
| `extra.ld` | `ld(p)`<br>`ld(p, scope=…, semantic=…)` | Per active element: access load, atomic scope/order; an empty spin on a word becomes a wait. | D5; A1(a), A3 | 8 | #81 |
| `extra.ld_acquire` | `ld_acquire(p, scope)` | Plain load. At L236 and L291 of the inter-node kernel, each empty spin is one plain wait. Its shmem writer conflicts with it (`conflict_of_plain`). | A3, W1; §9 item 10 | 1 | #81 |
| `extra.membar` | `membar(scope=…)` | Fence in plain mode; adds no order. | W2 | 2 | #81 |
| `extra.st` | `st(p, value)`<br>`st(p, value, scope=…, semantic=…)`<br>`st(p, value, semantic=…, scope=…)` | Per active element: access store, atomic scope/order. | D5; A1(a); A8 where cross-GPU | 10 | #81 |
| `extra.tid` | `tid(axis=…)`<br>`tid(axis)` | No event; thread coordinate on the requested axis. | E-TD8 | 13 | #81 |
| `shmem.barrier_all_block` | `libshmem_device.barrier_all_block()` | PE rendezvous with shmem release/acquire (M2). D2 limits visibility. At return, the calling agent’s earlier transfers have their matching completions, including signalling puts (M6 below). | E-NV13, E-NV15, E-NV16, D2, D4, D7 | 2 | #80 |
| `shmem.fence` | `libshmem_device.fence()` | Emit `Event.fence (.shmem .release)`. S4.1 constrains completion order for the same issuer and destination PE; the fence creates no synchronization edge. | E-NV1, E-NV3, D1, D7 | 3 | #80 |
| `shmem.getmem_block` | `libshmem_device.getmem_block(dest, src, bytes, pe)` | Initiate get (remote source, local destination), `nbi = false`; group initiation and its own completion in one S4.1 step before return (M1). | E-NV6, E-NV16, D4 | 1 | #80 |
| `shmem.getmem_nbi_block` | `libshmem_device.getmem_nbi_block(dest, src, bytes, pe)` | Initiate get (remote source, local destination), `nbi = true`; its delivery may remain pending at kernel exit (M1). | E-NV6, E-NV16, D4 | 2 | #80 |
| `shmem.putmem_block` | `libshmem_device.putmem_block(dest, src, bytes, pe)` | Initiate put (local source, remote destination), `nbi = false`; asynchronous completion bumps the issuer’s delivered counter (M1). | E-NV4, E-NV16, D4 | 2 | #80 |
| `shmem.putmem_nbi_block` | `libshmem_device.putmem_nbi_block(dest, src, bytes, pe)` | Initiate put (local source, remote destination), `nbi = true`; asynchronous completion bumps the issuer’s delivered counter (M1). | E-NV5, E-NV16, D4 | 3 | #80 |
| `shmem.putmem_signal_block` | `libshmem_device.putmem_signal_block(dest, src, bytes, sig, value, op, pe)` | Initiate put (local source, remote destination), `nbi = false`; complete with target signal word set/add. Asynchronous delivery. | E-NV8, E-NV12, E-NV16, D4 | 4 | #80 |
| `shmem.putmem_signal_nbi_block` | `libshmem_device.putmem_signal_nbi_block(dest, src, bytes, sig, value, op, pe)` | Initiate put (local source, remote destination), `nbi = true`; complete with target signal word set/add. Asynchronous delivery. | E-NV9, E-NV12, E-NV16, D4 | 2 | #80 |
| `shmem.putmem_signal_nbi_warp` | `libshmem_device.putmem_signal_nbi_warp(dest, src, bytes, sig, value, op, pe)` | Initiate put (local source, remote destination), `nbi = true`; complete with target signal word set/add. Asynchronous delivery. | E-NV9, E-NV12, E-NV16, D4 | 1 | #80 |
| `shmem.signal_op` | `libshmem_device.signal_op(p, value, op, pe)` | Bump the destination word, specified set/add and value, shmem release. | E-NV10, E-NV12 | 3 | #80 |
| `shmem.signal_wait_until` | `libshmem_device.signal_wait_until(p, cmp, value)` | Wait on word with supplied comparison/value, shmem acquire. Signal writers only. | E-NV11, E-NV12, E-NV21 | 4 | #80 |
| `tl.atomic_add` | `tl.atomic_add(p, value, mask=…, sem=…, scope=…)`<br>`tl.atomic_add(p, value, sem=…, scope=…)` | Masked, per-element access update in atomic scope/order; return old value for the binding form. | E-TR1; A1(d) | 2 | #81 |

## Event parameters and recorded decisions

- Each accepted memory order and scope pair uses the operation’s own registry entry. The default for `ld/st` is GPU/relaxed. The target forms bind `tl.atomic_add` and `atomic_add` results to the **previous** value. Only mask-true lanes emit an event. A2.1 checks vocabulary and argument shape; the implementing tickets validate operands, literals, launch conditions, and active masks.
- **M2 — CTA, grid and PE rendezvous.** `Counter.phase c 0` is the barrier object for `__syncthreads` in CTA `c`. D8 orders participating threads across each phase. For A9, cooperative launch is a precondition of the K-M launch contract. Encode the grid of a particular launch and rank as `Counter.rendezvous (2 * gridKey)`, using an injective key for that pair. Encode the PE team of that launch as `Counter.rendezvous (2 * teamKey + 1)`, using an injective key for the launch and team. Reuse each object across phases. Starting at zero, each member arrives once with a release `add 1`; at phase `k ≥ 1` the acquire wait is `ge (k * participantCount)`. Count threads for the CTA, blocks for the grid and PEs for the team. Use atomic CTA, atomic GPU and shmem modes respectively. The scheduler checks the roster and phase. Since these counters only increase, `Counter.ge_stable` preserves a met threshold. [Cooperative launch decision](https://github.com/VeriInfra-Lab/VeriTile-2/issues/467)
- **M1 — transfer completion.** For an unsignalled get or put, set `t.completion = some ⟨.delivered issuer, .add, 1, .shmem .release⟩`. The signed `Event.complete t` delivers the data and applies that private bump. Release supplies an edge to an eligible acquire. There is no acquire side to chain independent completions. A signalling put instead uses the remote signal word with the specified set/add and shmem release. The `nbi` flag follows the callee; D4 requires identical arguments across the participating warp or block.
- **Blocking return and pending gets.** For `getmem_block`, #80 emits initiation and its matching completion in one S4.1 (#47) step. The caller resumes with that get’s data delivered, regardless of earlier NBI traffic. Another delivery cannot release the caller. A blocking put permits source reuse at return while delivery may occur later (E-NV4). In `all_to_all_v_2d_kernel` (L291) and `_v2` (L454), no quiet or PE barrier follows the NBI gets. Their destinations may remain in flight at kernel exit. The K-M.4 host/launch contract (#183) must justify a completion boundary before K-M.5 (#184) uses the data. Without that evidence a completed-destination postcondition is unavailable. [Pinned offset kernels](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/kernels/nvidia/all_to_all_vdev_2d_offset.py#L291-L454)
- **Quiet and fence.** #80 supplies the operation and S4.1 (#47) the step constraints. At `quiet` entry take the calling agent’s earlier operations. Return only after every covered transfer has its matching completion. For unsignalled copies the acquire wait `(.delivered issuer) .ge n (.shmem .acquire)` uses the cumulative count of that issuer’s earlier unsignalled copies. Signalling puts require their matching completions as well: under the signed representation their signal bumps do not increment that counter. D7 excludes a guarantee for operations issued by another thread, and D2 governs which payload locations synchronization reaches. No selected root calls `quiet`. For a fence the step relation constrains completion order under E-NV1 per destination PE over the caller’s eligible prior blocking operations. The fence event carries no PE and its `releaseOf?` is `none`. D1 excludes a prior NBI put: at L215–230 in the inter-node kernel the signal can precede data delivery. #185 carries this finding. [Pinned fence sequence](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/kernels/nvidia/all_to_all_vdev_2d_offset_inter_node.py#L215-L230)
- An empty-body CAS spin is one wait plus a successful set in the same S4.1 step (#47). Under M3, a multi-word `dl.wait` observes each word in its own step and resumes after all observations. D6 requires the proof to hold for equality and greater-or-equal. A proof may rely on neither observation order nor interleaving with other agents.
- **Kernel findings.** In tutorial 07 the original CUDA-family wait conflicts with the shmem write. The proof targets a repaired single-family variant; the accepted extension includes matching host and device signal operations. In `all_to_all_v_2d_inter_node_kernel`, L236 and L291 spin via `ld_acquire` on words updated by `putmem_signal_nbi_warp` and `signal_op`. Each A3 spin is a W1 plain wait and races with the corresponding shmem write. The same conflict class remains a finding for K-M.6 (#185). M7 also leaves the prefix sums of the five roots that use the shuffle helpers unspecified. [Registry §9](https://github.com/VeriInfra-Lab/VeriTile-2/blob/main/documents/dist/PrimitiveSources.md#decisions-of-2026-11-23) · [Host signal decision on #489](https://github.com/VeriInfra-Lab/VeriTile-2/issues/489#issuecomment-7121319895)
- The base CUDA queries `tl.extra.cuda.num_threads()`, `tl.extra.cuda.num_warps()`, and `tl.extra.cuda.utils.num_warps()` are independent launch constants, supplied by the call signature. All three have **zero** uses in the 51 roots. Their eventual base-frontend adapter belongs to #77. The metadata queries are distinct from the `extra.num_threads/num_warps` registry entries. `tl.load(..., volatile=True)` is rejected. Profiling off gives `.record` the identity; profiling on fails. The scoped profiler calls route to #452. [Coverage matrix](../TritonSubset.md) · [Decisions on #78](https://github.com/VeriInfra-Lab/VeriTile-2/issues/78)
- For `common.next_power_of_2`, keep W3 in any theorem relying only on §5.8. Use the existing opt-in constexpr adapter and its exact pinned specialization when that stronger result is required. Its source spelling is already implemented; A2.1 adds no second parser. [Existing adapter](../../VeriTile/Dist/Frontend/TritonExt/Constexpr.lean)

## M6 — PE-barrier completion coverage

Like `quiet`, the PE barrier covers earlier operations issued by the calling agent. When it returns, each covered transfer has its matching completion, including the matching completion of each signalling put. D7 gives no completion guarantee for a transfer issued by another block or warp. [M6 decision on #78](https://github.com/VeriInfra-Lab/VeriTile-2/issues/78#issuecomment-7144445807)

In `all_to_all_v_2d_inter_node_kernel`, warps issue signalled NBI puts (L185–200), other blocks issue unsignalled NBI puts (L215), all blocks enter the grid rendezvous, and only `pid == 0` calls the closing `barrier_all_block` (L310). The rendezvous orders block participation. K-M.6 therefore cannot infer delivery of the other issuers’ puts when the elected block’s PE barrier returns. Each issuer can call `quiet` before entering the grid rendezvous, as in the tutorial 07 repair. [Pinned kernel](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/kernels/nvidia/all_to_all_vdev_2d_offset_inter_node.py#L185-L310) · [K-M.6 repair on #185](https://github.com/VeriInfra-Lab/VeriTile-2/issues/185)

The user rejected option (ii), which would publish a remote signal update and a private delivered increment in the same completion. It would require re-signing the S2 core, including `Transfer.completion` and `SyncEdge.of_complete`, while the original kernel would still fail on the independent spin conflict and NBI fence finding.

## Rejected names

These registry rows have no direct surface call in the selected roots or belong to another language/host. The W3 implementation helper `__shfl_sync_with_mode_i32` is reached internally by both W4 shuffle wrappers and has no independent supported surface form (M7). Each is excluded from the distributed grammar for the reason shown. Columns use suffixes relative to the indicated family. For the 25 NVSHMEM rows without a CUDA binding the registry supplies the additional backend reason. Constants, types, host utilities, and upstream base Triton expressions keep their respective grammar. An unidentified generic source-helper call may parse as an existing upstream identifier expression; it provides no A2 distributed binding. The same upstream grammar already parses the statement spelling of `tl.atomic_add` with generic keywords. The distributed syntax nodes and their elaborator require the scope. Under M5, 41 of 48 tested bodies fail to parse with the scope closed. Seven already parse as upstream zero/one-argument helper calls or `tl.atomic_add` statements; these must fail elaboration and produce no distributed node. This is the signed deviation from the ticket’s “parse fails” wording. The rejection tests pin the parser or elaborator diagnostic for every excluded call in both positions at all five tested arities. [M5 decision](https://github.com/VeriInfra-Lab/VeriTile-2/issues/78#issuecomment-7121319432) [Registry §§5.1–5.8](PrimitiveSources.md#5-tables)

| Family | Rejection reason | Names |
| --- | --- | --- |
| dl | No selected kernel calls these names | `extract`, `insert`, `vector`, `make_vector`, `zeros_vector`, `ld_vector`, `st_vector`, `SMEM_GENERIC_POINTER_ADDR_SPACE`, `SharedMemoryDesc`, `allocate_smem`, `smem_index`, `smem_load`, `smem_store`, `smem_get_ptr`, `get_smem_shared_address_u32`, `smem_dealloc`, `tma`, `extern_call` |
| dl.tma | No selected kernel calls these names | `create_tmap_2d`, `tmap_update_address`, `PipelineState`, `TmaPipeline`, `store_and_wait` |
| libshmem_device | No selected kernel calls these names | `set_rocshmem_ctx`, `my_pe`, `n_pes`, `team_my_pe`, `team_n_pes`, `int_p`, `remote_ptr`, `remote_mc_ptr`, `barrier_all`, `barrier_all_vec`, `barrier_all_warp`, `barrier_all_wave`, `barrier_all_wg`, `barrier`, `barrier_vec`, `barrier_block`, `barrier_warp`, `sync_all`, `sync_all_block`, `sync_all_warp`, `sync`, `team_sync_block`, `team_sync_warp`, `quiet`, `quiet_pe`, `getmem_nbi_warp`, `getmem_warp`, `getmem_nbi`, `getmem_nbi_wave`, `getmem_nbi_wg`, `getmem`, `getmem_wave`, `getmem_wg`, `putmem_warp`, `putmem_nbi_warp`, `putmem`, `putmem_wave`, `putmem_wg`, `putmem_nbi`, `putmem_nbi_wave`, `putmem_nbi_wg`, `putmem_signal_nbi`, `putmem_signal`, `putmem_signal_warp`, `putmem_signal_wave`, `putmem_signal_wg`, `putmem_signal_nbi_wave`, `putmem_signal_nbi_wg`, `uint64_wait_until_equals`, `ulong_put_signal`, `broadcastmem`, `broadcastmem_warp`, `broadcastmem_block`, `broadcast`, `broadcast_warp`, `broadcast_block`, `fcollectmem`, `fcollectmem_warp`, `fcollectmem_block`, `fcollect`, `fcollect_warp`, `fcollect_block`, `putmem_rma`, `putmem_rma_block`, `putmem_rma_warp`, `putmem_rma_nbi`, `putmem_rma_nbi_block`, `putmem_rma_nbi_warp`, `putmem_signal_rma`, `putmem_signal_rma_nbi`, `putmem_signal_rma_warp`, `putmem_signal_rma_nbi_warp`, `putmem_signal_rma_block`, `putmem_signal_rma_nbi_block`, `team_translate_pe` |
| language_extra | No direct selected surface call; the internal shuffle target has the W3 treatment above | `ld_vector`, `st_vector`, `pack`, `unpack`, `threads_per_warp`, `num_threads`, `num_warps`, `tl_type_to_ptx_suffix`, `__fence`, `tma_sync`, `load_v4_u32`, `load_v4_b32`, `load_v4_s32`, `load_v2_b64`, `st_v4_u32`, `st_v4_b32`, `st_v2_u32`, `multimem_st_b64`, `multimem_st_b32`, `multimem_st_v2`, `multimem_st_v4`, `multimem_st_p_b32`, `multimem_ld_reduce_p_v4`, `multimem_ld_reduce_v4`, `ntid`, `red_release`, `arrive_inc`, `arrive_inc_asm`, `ld_b32`, `st_b32`, `atomic_add_per_warp`, `wait_eq`, `__shfl_sync_with_mode_i32`, `__shfl_down_sync_i32`, `__shfl_xor_sync_i32`, `__ballot_sync`, `globaltimer_lo`, `globaltimer_hi`, `globaltimer`, `smid`, `fence`, `pack_b32_v2` |
| TileScale | TileScale surface | `fence_gpu`, `fence_sys`, `get_rank`, `get_num_ranks`, `put_warp`, `get_warp`, `put_block`, `get_block`, `ld`, `st`, `atom_add`, `wait_eq`, `wait_ne`, `wait_ge`, `wait_le`, `wait_gt`, `wait_lt`, `init_barrier_gpu`, `arrive_barrier_gpu`, `wait_barrier_gpu`, `sync_barrier_gpu`, `barrier_blocks`, `sync_blocks`, `multimem_ld_reduce`, `multimem_st`, `multimem_red`, `multimem_tma_store`, `multimem_signal`, `multimem_signal_add`, `copy`, `tma_copy`, `atomic_add`, `atomic_addx2` |
| TileScale host | Host operation of TileScale | `set_signal`, `wait_eq` |
| common_ops (host) | Called by tutorial host code | `set_signal`, `wait_eq` |

## Reproduce the coverage check

From the repository root, run the following Python block. It rebuilds the set of keys and the distinct-root counts from the committed generated census, including the recorded cross-file edges. A new or missing primitive, a changed count, or a new registry row without a disposition fails the check.

```sh
sed -n '/^```python$/,/^```$/{ /^```/d; p; }' documents/dist/TritonDistSubset.md | python3 -
```

```python
from collections import defaultdict
from pathlib import Path
import re

census = Path('documents/census/MinimalSyntax.md').read_text()
kernels, calls = census.split('### Triton-distributed: kernels\n')[1].split('### Triton-distributed: calls\n')
calls = calls.split('### Triton-distributed: statements')[0]
def rows(text):
    return [line.strip('|').strip().split(' | ') for line in text.splitlines() if line.startswith('| ')]
def numbers(ranges):
    result = set()
    for run in ranges.split(', '):
        lo, *hi = map(int, run.split('-'))
        result.update(range(lo, (hi or [lo])[0] + 1))
    return result

# The seven non-tutorial rows in the tutorial call graph in EventControlFlow §2.
reached = {'barrier_all_intra_node_atomic_cas_block', '_barrier_all_intra_node_non_atomic_once_block',
           'barrier_all_intra_node_non_atomic_block', 'kernel_ring_reduce_tma', 'kernel_ring_reduce_non_tma',
           'kernel_inter_node_p2p_for_same_local_rank', 'add_continuous_kernel'}
ids = {int(n): f.strip('`') for n, family, _, path, f, line in rows(kernels)[2:]
       if 'K-M' in family or 'tutorials/' in path or ('K-T' in family and f.strip('`') in reached)}
users = {name.strip('`'): numbers(ranges) & ids.keys() for name, _, _, ranges in rows(calls)[2:]}
common = 'triton_dist.kernels.nvidia.'
lang = 'triton_dist.language.'
# The report already follows same-file helpers. Propagate imported calls across the remaining edges.
for callee, qualified in [('single_block_prefix_sum_kernel_scan_scan', 'all_to_all_vdev_2d_offset'),
                          ('barrier_all_intra_node_atomic_cas_block', 'common_ops')]:
    root, = [i for i, f in ids.items() if f == callee]
    callers = users[common + qualified + '.' + callee]
    for using in users.values():
        if root in using:
            using.update(callers)
# The imported warp helper is inventoried in MoEInventory, imported warp_prefix_sum_kernel (line 43).
users[lang + 'extra.cuda.language_extra.__shfl_up_sync_i32'] = users[common + 'gemm_rs_threadblock_swizzle.warp_prefix_sum_kernel']

prefixes = [(lang+'extra.cuda.language_extra.', 'extra.'), (lang+'extra.language_extra.', 'extra.'),
            (lang+'extra.libshmem_device.', 'shmem.'), (lang, 'dl.'), (common+'common_ops.', 'common.'),
            ('triton_dist.tools.profiler.', ''), ('triton.language.atomic_add', 'tl.atomic_add'), ('.record', '.record')]
actual = defaultdict(set)
for name, using in users.items():
    for prefix, short in prefixes:
        if using and name.startswith(prefix):
            actual[short + name[len(prefix):]].update(using)
            break
doc = Path('documents/dist/TritonDistSubset.md').read_text()
listed = {key.strip('`'): int(count) for key, _, _, _, count, _ in rows(doc.split('## Target calls')[1].split('## ')[0])[2:]}
assert len(ids) == 51
expected = {k: len(v) for k, v in actual.items()}
assert listed == expected, (listed.items() - expected.items(), expected.items() - listed.items())
print(f'{len(ids)} roots, {len(listed)} mapped names; every count agrees')
registry = Path('documents/dist/PrimitiveSources.md').read_text()
sections = re.findall(r'^### 5\.(\d+)[^\n]*\n(.*?)(?=^### |^## )', registry, re.M | re.S)
prefixes = ['', 'dl.', 'dl.tma.', 'shmem.', 'extra.', 'T.', 'host.', '', '']
excluded = {family: set(re.findall(r'`([^`]+)`', names)) for family, _, names in
            rows(doc.split('## Rejected names')[1].split('## ')[0])[2:]}
families = ['', 'dl', 'dl.tma', 'libshmem_device', 'language_extra', 'TileScale',
            'TileScale host', 'common_ops (host)', 'common_ops']
assert len(sections) == 8
for n, body in sections:
    keys = {prefixes[int(n)] + k.replace('common_ops.', 'common.') for k in re.findall(r'^\| `([^`]+)` \|', body, re.M)}
    remaining = {key.rsplit('.', 1)[-1] for key in keys - listed.keys()}
    assert remaining == excluded.get(families[int(n)], set()), (n, remaining)
print('Registry partition agrees')
```
