# Location and agent model (S1)

This is a source-level crosswalk for the CUDA targets. The location model is
in [`Space`](../../VeriTile/Dist/Space.lean), [`Agent`](../../VeriTile/Dist/Agent.lean),
[`Accessible`](../../VeriTile/Dist/Access.lean),
[`AccessibleAt` and `symmAt`](../../VeriTile/Dist/SymmHeap.lean), and
[`ThreadGuard`](../../VeriTile/Dist/ThreadGuard.lean). The rows describe the
model's interpretation of the surface, not a promise about physical register
placement, compiler lowering, scheduling, memory ordering, or hardware
implementation. A dash means the referenced base-language surface does not
expose a separate object or agent at that level; it is not an additional
semantic assumption. References are to the project's pinned front-end
versions ([source policy](PrimitiveSources.md#1-rules),
[census pins](../../scripts/census/targets.tsv)). A pinned docstring is marked
as such.

## Spaces

| Space and lifetime in the model | Triton / Triton-distributed (`tl` / `dl`) | TileLang / TileScale (`T`) |
| --- | --- | --- |
| `global r` — kernel | Kernel tensor pointers, `tl.load` and `tl.store` ([Triton tutorial](https://github.com/triton-lang/triton/blob/0add68262ab0a2e33b84524346cb27cbb2787356/python/tutorials/01-vector-add.py#L29-L54)). For a symmetric allocation, `dl.symm_at(ptr, rank)` selects the corresponding peer address ([TD symmetric memory](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/docs/python-api/triton-dist.semantics.rst#L79-L92)). | `T.Tensor` arguments default to global storage ([TileLang](https://github.com/tile-ai/tilelang/blob/35850c06875bcc84751417982bf7b4d662bafdbc/docs/programming_guides/language_basics.md#L176-L183), [TileScale](https://github.com/tile-ai/tilescale/blob/71e71457d40ed6e6a2dad297936bfdbff21d104b/docs/programming_guides/language_basics.md#L119-L126)); TileScale `T.copy(..., src_pe=..., dst_pe=...)` remaps allocator-backed addresses ([allocation condition](https://github.com/tile-ai/tilescale/blob/71e71457d40ed6e6a2dad297936bfdbff21d104b/docs/distributed_api_reference.md#L106-L117), [peer API](https://github.com/tile-ai/tilescale/blob/71e71457d40ed6e6a2dad297936bfdbff21d104b/docs/distributed_api_reference.md#L183-L203)). |
| `shared c` — CTA | Base Triton delegates shared-memory allocation to the compiler ([programming guide](https://github.com/triton-lang/triton/blob/0add68262ab0a2e33b84524346cb27cbb2787356/docs/programming-guide/chapter-1/introduction.rst#L52-L56)). TD explicitly exposes `dl.allocate_smem`, `dl.smem_load`, `dl.smem_store` ([allocation docstring](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/language/smem_ops.py#L226-L239), [access docstrings](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/language/smem_ops.py#L321-L336)). | `T.alloc_shared(shape, dtype)` ([TileLang memory scopes](https://github.com/tile-ai/tilelang/blob/35850c06875bcc84751417982bf7b4d662bafdbc/docs/programming_guides/language_basics.md#L176-L188), [TileScale memory scopes](https://github.com/tile-ai/tilescale/blob/71e71457d40ed6e6a2dad297936bfdbff21d104b/docs/programming_guides/language_basics.md#L119-L131)). |
| `fragment c` — CTA | Logical tile values (e.g. `tl.arange`, tensor arithmetic); these are program-level values, not an explicit register allocation or a physical shared-memory alias ([Triton tensor docstring](https://github.com/triton-lang/triton/blob/0add68262ab0a2e33b84524346cb27cbb2787356/python/triton/language/core.py#L841-L849), [tutorial](https://github.com/triton-lang/triton/blob/0add68262ab0a2e33b84524346cb27cbb2787356/python/tutorials/01-vector-add.py#L44-L54)). | `T.alloc_fragment` is the logical tile in the shared programming view, even when implemented by distributed thread registers ([TileLang](https://github.com/tile-ai/tilelang/blob/35850c06875bcc84751417982bf7b4d662bafdbc/docs/programming_guides/language_basics.md#L178-L189), [TileScale](https://github.com/tile-ai/tilescale/blob/71e71457d40ed6e6a2dad297936bfdbff21d104b/docs/programming_guides/language_basics.md#L121-L132)). |
| `local c t` — thread | No distinct thread-local buffer allocator in the base tile surface ([program-level model](https://github.com/triton-lang/triton/blob/0add68262ab0a2e33b84524346cb27cbb2787356/docs/programming-guide/chapter-1/introduction.rst#L15-L49)); TD exposes a per-thread context `dl.simt_exec_region()` and scalar thread index `tid(axis)` ([SIMT context](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/docs/python-api/triton-dist.language.rst#L65-L76), [thread index](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/docs/python-api/triton-dist.language.rst#L164-L172)). The model tags thread-private state there, not arbitrary tile values. | `T.alloc_local(shape, dtype)` for thread-private storage ([TileLang docstring](https://github.com/tile-ai/tilelang/blob/35850c06875bcc84751417982bf7b4d662bafdbc/tilelang/language/allocate.py#L67-L77), [TileScale docstring](https://github.com/tile-ai/tilescale/blob/71e71457d40ed6e6a2dad297936bfdbff21d104b/tilelang/language/allocate.py#L52-L62)). |
| `barrier c` — CTA | TD barrier objects in `dl.tma.TmaPipeline` use shared allocations for the ready/empty mbarriers, with `init_barriers` ([docstring](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/language/tma/pipeline.py#L123-L139)). Block rendezvous itself (`__syncthreads`) is not a memory allocation ([TD API](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/docs/python-api/triton-dist.language.rst#L193-L195)). | `T.alloc_barrier(arrive_count)` ([TileLang reference](https://github.com/tile-ai/tilelang/blob/35850c06875bcc84751417982bf7b4d662bafdbc/docs/programming_guides/instructions.md#L268-L271), [TileScale reference](https://github.com/tile-ai/tilescale/blob/71e71457d40ed6e6a2dad297936bfdbff21d104b/docs/programming_guides/instructions.md#L151-L156)). This is a CTA object, not the cross-GPU signal word. |
| `tmem c` — CTA (tag only) | No separate TMEM allocation in the base `tl` surface ([language API](https://github.com/triton-lang/triton/blob/0add68262ab0a2e33b84524346cb27cbb2787356/docs/python-api/triton.language.rst)); experimental Triton Gluon has `allocate_tensor_memory` ([docstring](https://github.com/triton-lang/triton/blob/0add68262ab0a2e33b84524346cb27cbb2787356/python/triton/experimental/gluon/language/nvidia/blackwell/__init__.py#L301-L314)). This is a location cross-reference, not admission of a Gluon or TD operation. | `T.alloc_tmem(shape, dtype)` on Blackwell or later ([TileLang](https://github.com/tile-ai/tilelang/blob/35850c06875bcc84751417982bf7b4d662bafdbc/docs/programming_guides/instructions.md#L170-L175), [TileScale](https://github.com/tile-ai/tilescale/blob/71e71457d40ed6e6a2dad297936bfdbff21d104b/docs/programming_guides/instructions.md#L151-L156)). |

In the Lean model a region outside its lifetime is not live. Accessibility is
separate: the CTA-owned spaces (`shared`, `fragment`, `barrier`, `tmem`) admit
only their CTA and its descendants; `local` admits its owning thread identity
(within the CTA). `Accessible` accepts every global space, but `AccessibleAt`
requires symmetric membership for a peer's cell. Symmetric remapping keeps
region and offset and changes the rank; it does not make every pointer remote.
The kernel lifetime of global memory is the model's validity interval, not a
claim that the host allocation is freed at kernel return.

## Agents

| Agent in the model | Triton / Triton-distributed | TileLang / TileScale |
| --- | --- | --- |
| `rank r` — one GPU of the launch | `dl.rank()` / `dl.num_ranks()` ([TD API](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/docs/python-api/triton-dist.language.rst#L33-L45)). Base Triton launches on a device; it does not expose this distributed rank query ([tutorial device selection](https://github.com/triton-lang/triton/blob/0add68262ab0a2e33b84524346cb27cbb2787356/python/tutorials/01-vector-add.py#L23-L39)). | TileScale `T.get_rank()` / `T.get_num_ranks()` refer to the local process group, with documented rank-to-device mapping ([host mapping](https://github.com/tile-ai/tilescale/blob/71e71457d40ed6e6a2dad297936bfdbff21d104b/docs/distributed_api_reference.md#L46-L58), [rank queries](https://github.com/tile-ai/tilescale/blob/71e71457d40ed6e6a2dad297936bfdbff21d104b/docs/distributed_api_reference.md#L171-L181)). Base TileLang's launch indices are program indices, not rank ids ([guide](https://github.com/tile-ai/tilelang/blob/35850c06875bcc84751417982bf7b4d662bafdbc/docs/programming_guides/language_basics.md#L87-L114)). |
| `cta c` — program/block on a rank | `tl.program_id(axis)` gives the current program's grid coordinate ([Triton docstring](https://github.com/triton-lang/triton/blob/0add68262ab0a2e33b84524346cb27cbb2787356/python/triton/language/core.py#L1598-L1605)); it is paired with rank in the model. | `with T.Kernel(grid_x, grid_y, threads=...) as (bx, by)` ([TileLang](https://github.com/tile-ai/tilelang/blob/35850c06875bcc84751417982bf7b4d662bafdbc/docs/programming_guides/language_basics.md#L87-L114), [TileScale](https://github.com/tile-ai/tilescale/blob/71e71457d40ed6e6a2dad297936bfdbff21d104b/docs/programming_guides/language_basics.md#L82-L93)). |
| `group c g` — role or warp group within a CTA | Base Triton `tl.range(..., warp_specialize=True)` requests compiler-chosen partitions, not a group-id query ([docstring](https://github.com/triton-lang/triton/blob/0add68262ab0a2e33b84524346cb27cbb2787356/python/triton/language/core.py#L3239-L3253)). TD roles can be expressed by a partition of `tid(0)` using `threads_per_warp()` in a SIMT region ([thread query](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/docs/python-api/triton-dist.language.rst#L164-L172), [warp-size query](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/docs/python-api/triton-dist.language.rst#L241-L251)); group membership is the source partition, not an inferred fixed assignment. | `T.get_warp_group_idx(warp_size, warps_per_group)` ([TileLang reference](https://github.com/tile-ai/tilelang/blob/35850c06875bcc84751417982bf7b4d662bafdbc/docs/programming_guides/instructions.md#L281-L285), [TileScale docstring](https://github.com/tile-ai/tilescale/blob/71e71457d40ed6e6a2dad297936bfdbff21d104b/tilelang/language/builtin.py#L663-L685)); a source role may instead be a thread-index partition. |
| `thread c g t` — thread within its group and CTA | Base Triton programs abstract over individual threads ([programming model](https://github.com/triton-lang/triton/blob/0add68262ab0a2e33b84524346cb27cbb2787356/docs/programming-guide/chapter-1/introduction.rst#L15-L49)); TD `tid(axis)`, e.g. a `tid(0) == 0` guard in a one-dimensional CTA ([TD API](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/docs/python-api/triton-dist.language.rst#L164-L172)). | `T.get_thread_binding(dim=0)`, e.g. a `== 0` guard in a one-dimensional CTA ([TileLang guide](https://github.com/tile-ai/tilelang/blob/35850c06875bcc84751417982bf7b4d662bafdbc/docs/programming_guides/language_basics.md#L107-L115), [TileScale docstring](https://github.com/tile-ai/tilescale/blob/71e71457d40ed6e6a2dad297936bfdbff21d104b/tilelang/language/kernel.py#L445-L452)). |

The hierarchy is `rank → cta → group → thread`. `Scope.covers` is a separate
relation (`cta < gpu < sys`): GPU scope cannot cover two ranks. The exact
scope and order supported by each operation come from
[PrimitiveSources.md](PrimitiveSources.md), not this crosswalk. In particular,
TileScale's distributed `T.atom_add` admits `gpu` and `sys` in its documented
interface ([reference](https://github.com/tile-ai/tilescale/blob/71e71457d40ed6e6a2dad297936bfdbff21d104b/docs/distributed_api_reference.md#L211-L235));
this row does not give `cta` scope to a primitive that documents only those two.

## Regression target

Run `lake build tests.lean.dist.Location` (also in `scripts/local_gate.sh`
and the Dist CI shard). Its examples reject an ended CTA's shared storage and
an ended thread's local storage, cross-rank GPU scope, cross-CTA shared access,
non-symmetric remapping and non-symmetric peer access, and check rank-specific
name separation and launch-grid arity. Admitted controls vary
the corresponding lifetime, rank, owner, and symmetric-region premise. The
two-thread S1.6 run has a race without the guard and no race in the particular
completed `tid == 0` run, reusing the execution witnesses and testing their
write footprints. This last result is not a general data-race-freedom theorem.
The earlier location-layer checks prove rejection rather than a value-level
execution result.
