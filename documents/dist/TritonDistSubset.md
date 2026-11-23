# Triton-distributed surface and event mapping

Unsigned A2.1 proposal for tutorials 01–08 and the Triton-distributed K-M kernels at `7908e4ea9010bb2238f9f05b28c904fd4b71c60a`. Open `VeriTile.Dist.Frontend.TritonDist` after importing its `Syntax` module. A recognized distributed form reports its implementation ticket when elaborated. The mapping is a proposal for those implementations.

## Target calls

The source inventory uses 51 distinct roots from the generated Triton-distributed kernel index: every K-M row, the fourteen tutorial functions, and the seven common/reduce-scatter functions reached by the tutorials. Tutorial 04 belongs to both families and counts once. A root uses a primitive if it calls it directly or through a kernel-side helper. Host launches identify roots but do not charge all the primitive uses of the launched kernel to its caller. K-M’s additional host-launched `threadblock_swizzle_ag_moe_kernel` is inventoried separately in the MoE report (it uses the already listed `tid`, `__syncthreads`, `tl.atomic_add` and `next_power_of_2`). The counts exclude that extra root. Imported `warp_prefix_sum_kernel` is followed from every caller. The A9 wrapper counts as a call at its registered cooperative boundary. [Generated census](../census/MinimalSyntax.md#triton-distributed-kernels) · [Tutorial reachability, §2](EventControlFlow.md#2-sources) · [MoE census and imported functions](MoEInventory.md)

Each registry key uses its section of [PrimitiveSources](PrimitiveSources.md#5-tables): `dl` §5.1, `shmem` §5.3, `extra` §5.4, `tl.atomic_add` §5.7, `common` §5.8. The surface column gives the source spellings, including unqualified imports. Each row cites the evidence or rule IDs in that registry; the profiler decision is separate. The semantics column uses the [signed event interface](../../VeriTile/Staging/Dist/EventSpec.lean). Expression arguments and literal byte counts are evaluated by the calling program. A counter names an address, a CTA phase, a rendezvous, or the deliveries of an issuing agent.

| Registry key | Observed surface | Proposed event or local result | Evidence / treatment | Roots | Implementation |
| --- | --- | --- | --- | ---: | --- |
| `.record` | `profiler.record(is_start=…, task_type=…)` | Identity when profiling is off; refuse an enabled profiler. | Decision #452 | 3 | #452 |
| `Profiler.create` | `Profiler.create(profiler_buffer=…, group_id=…, num_groups=…, is_leader=…, ENABLE_PROFILING=…)` | Construct disabled profiler state when profiling is off. Active profiling is outside the subset. | Decision #452 | 3 | #452 |
| `common.barrier_all_intra_node_atomic_cas_block` | `barrier_all_intra_node_atomic_cas_block(localRank, rank, localSize, flags)` | Inline the two CAS spins and the block barrier; each uses its own event row. | W4; A1(b), A3, A8, D8 | 6 | #82 |
| `common.barrier_on_this_grid` | `barrier_on_this_grid(p, use_cooperative=…)`<br>`barrier_on_this_grid(p, cooperative)` | Under a cooperative launch: grid-wide arrival and wait with ordering. Use a launch-specific rendezvous. Otherwise W4. | A9; W4 outside premise | 6 | #82 |
| `common.next_power_of_2` | `next_power_of_2(n)` | No event. The registered W3 reading leaves the value unspecified. The existing constexpr extension separately specializes its pinned body. | W3, §5.8 | 2 | #449 |
| `dl.consume_token` | `dl.consume_token(value, token)` | No event; use the value after its wait token in the same agent. | E-TD2, E-TD4 | 6 | #79 |
| `dl.notify` | `dl.notify(p, rank, signal=…, comm_scope=…)`<br>`dl.notify(p, rank, signal=…, sig_op=…, comm_scope=…)` | Remote word bump, set (default) or add, release; `intra_node` → atomic sys, `gpu` → atomic gpu. | A2; A8 where cross-GPU | 2 | #79 |
| `dl.num_ranks` | `dl.num_ranks()` | No event; number of participating ranks. | E-TD6 | 7 | #79 |
| `dl.rank` | `dl.rank()` | No event; caller rank. | E-TD6 | 7 | #79 |
| `dl.simt_exec_region` | `with dl.simt_exec_region() as (thread, size)` | No event on entry; bind the thread index and block size for the enclosed SIMT program. | E-TD9 | 9 | #79 |
| `dl.symm_at` | `dl.symm_at(p, rank)` | No event; symmetric address on the designated rank. Later accesses keep their own mode. | E-TD5 | 12 | #79 |
| `dl.wait` | `dl.wait(p, count, scope=…, semantic=…, waitValue=…)`<br>`dl.wait(p, count, scope, semantic)`<br>`dl.wait(p, count, scope, semantic, waitValue=…)` | Word wait for each addressed element, mode `atomic scope order`; prove both eq and ge. A returned token carries the dependency. | E-TD1–3, D5, D6; A1(a) | 6 | #79 |
| `extra.__shfl_sync_i32` | `__shfl_sync_i32(mask, value, lane)` | Ordinary front-end helper by its body. No extra rendezvous or visibility edge. | W4 | 5 | #81 |
| `extra.__shfl_up_sync_i32` | `__shfl_up_sync_i32(mask, value, delta)` | Ordinary front-end helper by its body. Reached via the imported warp prefix sum. | W4 | 5 | #81 |
| `extra.__syncthreads` | `__syncthreads()` | Phase counter of this CTA; each participant arrives and waits, ordering accesses across the phase. | E-TD8, E-CU7, D8 | 20 | #81 |
| `extra.atomic_add` | `atomic_add(p, value, scope=…, semantic=…)`<br>`atomic_add(p, value, semantic=…, scope=…)` | Per element: access update, atomic scope/order; return old value even when the caller discards it. | D5; A1(a,b) | 5 | #81 |
| `extra.atomic_cas` | `atomic_cas(p, old, new, scope, semantic)` | Strong compare-exchange returning the observed value. For the empty-body spin, wait and successful set on the same word in one step; retain the source scope/order. | D5; A1(a,b), A3, A8 | 7 | #81 |
| `extra.laneid` | `laneid()` | No event; unspecified value. | W3 | 5 | #81 |
| `extra.ld` | `ld(p)`<br>`ld(p, scope=…, semantic=…)` | Per active element: access load, atomic scope/order; an empty spin on a word becomes a wait. | D5; A1(a), A3 | 8 | #81 |
| `extra.ld_acquire` | `ld_acquire(p, scope)` | Access load in plain mode. The argument conveys no synchronization guarantee. | W1; §9 item 10 | 1 | #81 |
| `extra.membar` | `membar(scope=…)` | Fence in plain mode; adds no order. | W2 | 2 | #81 |
| `extra.st` | `st(p, value)`<br>`st(p, value, scope=…, semantic=…)`<br>`st(p, value, semantic=…, scope=…)` | Per active element: access store, atomic scope/order. | D5; A1(a); A8 where cross-GPU | 10 | #81 |
| `extra.tid` | `tid(axis=…)`<br>`tid(axis)` | No event; thread coordinate on the requested axis. | E-TD8 | 13 | #81 |
| `shmem.barrier_all_block` | `libshmem_device.barrier_all_block()` | Collective rendezvous across PEs; bump then wait in shmem mode, with completion and visibility subject to ShmemReach. | E-NV13, E-NV15, E-NV16, D2, D4, D7 | 2 | #80 |
| `shmem.fence` | `libshmem_device.fence()` | Fence, shmem release, per destination PE for the caller’s eligible prior operations. | E-NV1, E-NV3, D1, D7 | 3 | #80 |
| `shmem.getmem_block` | `libshmem_device.getmem_block(dest, src, bytes, pe)` | Initiate get (remote source, local destination), `nbi = false`; complete with delivery bookkeeping. By return. | E-NV6, E-NV16, D4 | 1 | #80 |
| `shmem.getmem_nbi_block` | `libshmem_device.getmem_nbi_block(dest, src, bytes, pe)` | Initiate get (remote source, local destination), `nbi = true`; complete with delivery bookkeeping. Asynchronous delivery. | E-NV6, E-NV16, D4 | 2 | #80 |
| `shmem.putmem_block` | `libshmem_device.putmem_block(dest, src, bytes, pe)` | Initiate put (local source, remote destination), `nbi = false`; complete with delivery bookkeeping. Asynchronous delivery. | E-NV4, E-NV16, D4 | 2 | #80 |
| `shmem.putmem_nbi_block` | `libshmem_device.putmem_nbi_block(dest, src, bytes, pe)` | Initiate put (local source, remote destination), `nbi = true`; complete with delivery bookkeeping. Asynchronous delivery. | E-NV5, E-NV16, D4 | 3 | #80 |
| `shmem.putmem_signal_block` | `libshmem_device.putmem_signal_block(dest, src, bytes, sig, value, op, pe)` | Initiate put (local source, remote destination), `nbi = false`; complete with target signal word set/add. Asynchronous delivery. | E-NV8, E-NV12, E-NV16, D4 | 4 | #80 |
| `shmem.putmem_signal_nbi_block` | `libshmem_device.putmem_signal_nbi_block(dest, src, bytes, sig, value, op, pe)` | Initiate put (local source, remote destination), `nbi = true`; complete with target signal word set/add. Asynchronous delivery. | E-NV9, E-NV12, E-NV16, D4 | 2 | #80 |
| `shmem.putmem_signal_nbi_warp` | `libshmem_device.putmem_signal_nbi_warp(dest, src, bytes, sig, value, op, pe)` | Initiate put (local source, remote destination), `nbi = true`; complete with target signal word set/add. Asynchronous delivery. | E-NV9, E-NV12, E-NV16, D4 | 1 | #80 |
| `shmem.signal_op` | `libshmem_device.signal_op(p, value, op, pe)` | Bump the destination word, specified set/add and value, shmem release. | E-NV10, E-NV12 | 3 | #80 |
| `shmem.signal_wait_until` | `libshmem_device.signal_wait_until(p, cmp, value)` | Wait on word with supplied comparison/value, shmem acquire. Signal writers only. | E-NV11, E-NV12, E-NV21 | 4 | #80 |
| `tl.atomic_add` | `tl.atomic_add(p, value, mask=…, sem=…, scope=…)`<br>`tl.atomic_add(p, value, sem=…, scope=…)` | Masked, per-element access update in atomic scope/order; return old value for the binding form. | E-TR1; A1(d) | 2 | #81 |

## Event parameters and review choices

- Each accepted memory order and scope pair uses the operation’s own registry entry. The default for `ld/st` is GPU/relaxed. The target forms bind `tl.atomic_add` and `atomic_add` results to the **previous** value. Only mask-true lanes emit an event. A2.1 checks vocabulary and argument shape; the implementing tickets validate operands, literals, launch conditions, and active masks.
- A thread’s `__syncthreads` release arrival / acquire wait uses `Counter.phase c id` at CTA scope; D8 orders participating block threads. A9 applies only to the wrapper. A cooperative grid is a K-M launch-contract precondition (user decision 2026-11-23 on #467). For its event, use a fresh `Counter.rendezvous id` for that grid and phase, atomic GPU release arrivals and acquire waits. A rank barrier uses its own rendezvous, shmem release/acquire. Keep the two identities disjoint. The scheduler must track arrivals by participant and phase.
- `Event.initiate t` is the call; delivery is a separate `Event.complete t` attributed to the issuer. Propose `t.completion = some` with the target signal-word bump in shmem release mode for signalling operations, or with a private `Counter.delivered issuer` increment for an ordinary copy. In the signed interface `none` denotes a transfer without a completion. Representing a private delivery counter here avoids strengthening plain copies into user-visible signal writes. The nonblocking flag follows the actual call. For a blocking put only its source is reusable at return; a blocking get has delivered locally at return. D4 requires identical arguments across the participating warp or block. Preserve D1, D2 and D7 for delivery/order/visibility.
- An empty-body CAS spin is **one** wait plus successful set in the **same** step. S4.1 owns grouped-event representation and continuation values. For a multi-word `dl.wait` under D6, both equality and greater-or-equal readings must hold for the proof. How sequential word observations combine into a continuation is a review choice; a single atomic snapshot would add a guarantee absent from the registry.
- Tutorial 07’s original wait uses `atomic gpu acquire` on the same word that NVSHMEM completes in shmem mode. The signed conflict rule applies. The original as written is unprovable; the intended proof is of a repaired single-family variant (user decision 2026-11-23). Host-side signal helpers retain their §5.7 treatments. [Signed conflict theorem](../../VeriTile/Staging/Dist/EventSpec.lean) · [Decision on #78](https://github.com/VeriInfra-Lab/VeriTile-2/issues/78)
- The base CUDA queries `tl.extra.cuda.num_threads()`, `tl.extra.cuda.num_warps()`, and `tl.extra.cuda.utils.num_warps()` are independent launch constants, supplied by the call signature. All three have **zero** uses in the 51 roots. Their eventual base-frontend adapter belongs to #77. The metadata queries are distinct from the `extra.num_threads/num_warps` registry entries. `tl.load(..., volatile=True)` is rejected. Profiling off gives `.record` the identity; profiling on fails. The scoped profiler calls route to #452. [Coverage matrix](../TritonSubset.md) · [Decisions on #78](https://github.com/VeriInfra-Lab/VeriTile-2/issues/78)
- For `common.next_power_of_2`, keep W3 in any theorem relying only on §5.8. Use the existing opt-in constexpr adapter and its exact pinned specialization when that stronger result is required. Its source spelling is already implemented; A2.1 adds no second parser. [Existing adapter](../../VeriTile/Dist/Frontend/TritonExt/Constexpr.lean)

## Rejected names

These registry rows have zero calls in the selected roots or belong to another language/host. Each is excluded from the distributed grammar for the reason shown. Columns use suffixes relative to the indicated family. For the 25 NVSHMEM rows without a CUDA binding the registry supplies the additional backend reason. Constants, types, host utilities, and upstream base Triton expressions keep their respective grammar. An unidentified generic source-helper call may parse as an existing upstream identifier expression; it provides no A2 distributed binding. The same upstream grammar already parses the statement spelling of `tl.atomic_add` with generic keywords. The distributed syntax nodes require the scope. [Registry §§5.1–5.8](PrimitiveSources.md#5-tables)

| Family | Rejection reason | Names |
| --- | --- | --- |
| dl | No selected kernel calls these names | `extract`, `insert`, `vector`, `make_vector`, `zeros_vector`, `ld_vector`, `st_vector`, `SMEM_GENERIC_POINTER_ADDR_SPACE`, `SharedMemoryDesc`, `allocate_smem`, `smem_index`, `smem_load`, `smem_store`, `smem_get_ptr`, `get_smem_shared_address_u32`, `smem_dealloc`, `tma`, `extern_call` |
| dl.tma | No selected kernel calls these names | `create_tmap_2d`, `tmap_update_address`, `PipelineState`, `TmaPipeline`, `store_and_wait` |
| libshmem_device | No selected kernel calls these names | `set_rocshmem_ctx`, `my_pe`, `n_pes`, `team_my_pe`, `team_n_pes`, `int_p`, `remote_ptr`, `remote_mc_ptr`, `barrier_all`, `barrier_all_vec`, `barrier_all_warp`, `barrier_all_wave`, `barrier_all_wg`, `barrier`, `barrier_vec`, `barrier_block`, `barrier_warp`, `sync_all`, `sync_all_block`, `sync_all_warp`, `sync`, `team_sync_block`, `team_sync_warp`, `quiet`, `quiet_pe`, `getmem_nbi_warp`, `getmem_warp`, `getmem_nbi`, `getmem_nbi_wave`, `getmem_nbi_wg`, `getmem`, `getmem_wave`, `getmem_wg`, `putmem_warp`, `putmem_nbi_warp`, `putmem`, `putmem_wave`, `putmem_wg`, `putmem_nbi`, `putmem_nbi_wave`, `putmem_nbi_wg`, `putmem_signal_nbi`, `putmem_signal`, `putmem_signal_warp`, `putmem_signal_wave`, `putmem_signal_wg`, `putmem_signal_nbi_wave`, `putmem_signal_nbi_wg`, `uint64_wait_until_equals`, `ulong_put_signal`, `broadcastmem`, `broadcastmem_warp`, `broadcastmem_block`, `broadcast`, `broadcast_warp`, `broadcast_block`, `fcollectmem`, `fcollectmem_warp`, `fcollectmem_block`, `fcollect`, `fcollect_warp`, `fcollect_block`, `putmem_rma`, `putmem_rma_block`, `putmem_rma_warp`, `putmem_rma_nbi`, `putmem_rma_nbi_block`, `putmem_rma_nbi_warp`, `putmem_signal_rma`, `putmem_signal_rma_nbi`, `putmem_signal_rma_warp`, `putmem_signal_rma_nbi_warp`, `putmem_signal_rma_block`, `putmem_signal_rma_nbi_block`, `team_translate_pe` |
| language_extra | No selected kernel calls these names | `ld_vector`, `st_vector`, `pack`, `unpack`, `threads_per_warp`, `num_threads`, `num_warps`, `tl_type_to_ptx_suffix`, `__fence`, `tma_sync`, `load_v4_u32`, `load_v4_b32`, `load_v4_s32`, `load_v2_b64`, `st_v4_u32`, `st_v4_b32`, `st_v2_u32`, `multimem_st_b64`, `multimem_st_b32`, `multimem_st_v2`, `multimem_st_v4`, `multimem_st_p_b32`, `multimem_ld_reduce_p_v4`, `multimem_ld_reduce_v4`, `ntid`, `red_release`, `arrive_inc`, `arrive_inc_asm`, `ld_b32`, `st_b32`, `atomic_add_per_warp`, `wait_eq`, `__shfl_sync_with_mode_i32`, `__shfl_down_sync_i32`, `__shfl_xor_sync_i32`, `__ballot_sync`, `globaltimer_lo`, `globaltimer_hi`, `globaltimer`, `smid`, `fence`, `pack_b32_v2` |
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
