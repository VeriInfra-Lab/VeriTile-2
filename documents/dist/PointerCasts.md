# Pointer casts in the distributed tutorials, DeepEP v1 and P2P reads

## Scope and counting

This inventory covers the 44 sites from step 1 of #448 and 13 additional P2P kernel sites from the partial #593 inventory. Step 1 examined the eight Triton-distributed tutorial files in the map and their reached device kernels, including the seven library kernels/helpers in the tutorial call graph (21 kernel definitions in all). It also examined the five Python files in the pinned TileScale DeepEP v1 intranode directory. The #593 addition covers the fused and non-fused read kernels in the pinned P2P implementation. The original #448 target list also includes other families, including K-M. They count roots, whereas this inventory counts source expressions once across all callers. The source pins are Triton-distributed `7908e4ea9010bb2238f9f05b28c904fd4b71c60a` and TileScale `9ba8a605d347f600a95d0275e2639cb00122c084`. Step-1 sources were inspected on 2026-11-23 and the P2P read sites on 2026-11-25. [Tutorial call graph](EventControlFlow.md#2-sources) · [DeepEP v1 intranode directory](https://github.com/tile-ai/tilescale/tree/9ba8a605d347f600a95d0275e2639cb00122c084/examples/distributed/deepseek_deepep/intranode)

The map excludes tutorial 03a, including its two casts of `symm_ptr` to an int8 pointer. [Map scope](EventControlFlow.md#2-sources) · [T03a:89–91](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/tutorials/03a-inter-node-allgather.py#L89-L91)

A site in these tables is one pointer-targeting `tl.cast` or `.to`, one addition to the cast pointer (including an addition in the same expression as the cast, a chained addition or a later `+=`), or one `tl.cast` carrying any of `dtype=`, `bitcast=`, `_semantic=`. An expression matching two cast selectors counts once. Multiplying two integer indices counts as part of the offset. Lines shared by separate additions are identified by the operand. The second table follows reached front-end primitive wrappers to their external-call or inline-assembly boundary and reports their sites separately. No external code was run.

## Kernel sites

The before/after column gives the element type of the base pointer on the tutorial launch and the type used by the operation. The displacement is in bytes. For a cast by itself the added displacement is zero. **I** means the producer and consumer retain the payload's element interpretation on the cited path; **II** means different typed accesses to the same payload are visible in the source-level path. BF16 is two bytes, FP8 E4M3 and int8 each one. These are inferences from the source uses, not claims about physical accesses issued by a compiler.

| Site | Operation | Before → after | Byte displacement and divisibility | Writer/reader evidence |
| --- | --- | --- | --- | --- |
| [T03:86](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/tutorials/03-inter-node-allgather.py#L86) | destination cast | int8 → int8 | 0 | I. Byte copy; T03 allocation and comparison below. |
| [T03:86](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/tutorials/03-inter-node-allgather.py#L86) | destination add | int8 → int8 | `segment * bytes_per_rank`; divisible by 1 | I. Byte copy; T03 allocation and comparison below. |
| [T03:88](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/tutorials/03-inter-node-allgather.py#L88) | source cast | int8 → int8 | 0 | I. Byte copy; T03 allocation and comparison below. |
| [T03:88](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/tutorials/03-inter-node-allgather.py#L88) | source add | int8 → int8 | `segment * bytes_per_rank`; divisible by 1 | I. Byte copy; T03 allocation and comparison below. |
| [T03:132](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/tutorials/03-inter-node-allgather.py#L132) | rebind pointer by cast | int8 → int8 | 0 | I. Byte copy; T03 allocation and comparison below. |
| [T03:140](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/tutorials/03-inter-node-allgather.py#L140) | destination add, inter-node | int8 → int8 | `segment * bytes_per_rank`; divisible by 1 | I. Byte copy; T03 allocation and comparison below. |
| [T03:141](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/tutorials/03-inter-node-allgather.py#L141) | source add, inter-node | int8 → int8 | `segment * bytes_per_rank`; divisible by 1 | I. Byte copy; T03 allocation and comparison below. |
| [T03:170](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/tutorials/03-inter-node-allgather.py#L170) | destination add, intra-node | int8 → int8 | `segment * bytes_per_rank`; divisible by 1 | I. Byte copy; T03 allocation and comparison below. |
| [T03:171](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/tutorials/03-inter-node-allgather.py#L171) | source add, intra-node | int8 → int8 | `segment * bytes_per_rank`; divisible by 1 | I. Byte copy; T03 allocation and comparison below. |
| [T04:192](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/tutorials/04-deepseek-infer-all2all.py#L192) | cast dispatch send pointer | BF16 → FP8 | 0 at cast; pre-cast base advances by `2 * m_st * HIDDEN`; divisible by final FP8 size 1 | II, dispatch |
| [T04:192](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/tutorials/04-deepseek-infer-all2all.py#L192) | add `group_offs` | FP8 → FP8 | `row * HIDDEN + lane`; a lane can be odd; divisible by final FP8 size 1 | II, dispatch |
| [T04:212](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/tutorials/04-deepseek-infer-all2all.py#L212) | advance inner loop | FP8 → FP8 | `4 * FP8_GSIZE`; divisible by final FP8 size 1 | II, dispatch |
| [T04:215](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/tutorials/04-deepseek-infer-all2all.py#L215) | advance outer loop | FP8 → FP8 | `(BM - 1) * HIDDEN`; divisible by final FP8 size 1 | II, dispatch |
| [T04:350](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/tutorials/04-deepseek-infer-all2all.py#L350) | cast reference output | BF16 → FP8 | 0; divisible by final FP8 size 1 | I, reference |
| [T04:350](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/tutorials/04-deepseek-infer-all2all.py#L350) | add row (inner addition) | FP8 → FP8 | `off_m * N`; divisible by final FP8 size 1 | I, reference |
| [T04:350](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/tutorials/04-deepseek-infer-all2all.py#L350) | add column (outer addition) | FP8 → FP8 | `off_n`; includes odd lanes; divisible by final FP8 size 1 | I, reference |
| [T04:370](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/tutorials/04-deepseek-infer-all2all.py#L370) | advance output pointer | FP8 → FP8 | `4 * FP8_GSIZE`; divisible by final FP8 size 1 | I, reference |
| [T04:387](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/tutorials/04-deepseek-infer-all2all.py#L387) | cast dequant input | BF16 → FP8 | 0; divisible by final FP8 size 1 | II, dispatch; I on reference path |
| [T04:387](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/tutorials/04-deepseek-infer-all2all.py#L387) | add row (inner addition) | FP8 → FP8 | `off_m * N`; divisible by final FP8 size 1 | II, dispatch; I on reference path |
| [T04:387](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/tutorials/04-deepseek-infer-all2all.py#L387) | add column (outer addition) | FP8 → FP8 | `off_n`; includes odd lanes; divisible by final FP8 size 1 | II, dispatch; I on reference path |
| [T04:405](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/tutorials/04-deepseek-infer-all2all.py#L405) | advance input pointer | FP8 → FP8 | `4 * FP8_GSIZE`; divisible by final FP8 size 1 | II, dispatch; I on reference path |

**T03 byte copies.** The allocated buffer is int8, the launch receives an int8 slice, the two wrappers compute `bytes_per_rank = symm_buffer.nbytes // num_ranks`, and the result is compared with int8 data. There is no requirement that the segment start be divisible by a wider element size in these launches. The host separately constructs random int32 reference data and views it as int8 before copying it into the int8 buffer; that host view is outside the kernel-cast count. [Allocation](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/tutorials/03-inter-node-allgather.py#L268) · [1D launch](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/tutorials/03-inter-node-allgather.py#L98-L106) · [2D launch](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/tutorials/03-inter-node-allgather.py#L180-L191) · [Host producer and consumer](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/tutorials/03-inter-node-allgather.py#L196-L223)

**T04 dispatch.** The send and receive buffers are allocated with BF16 elements. In the online FP8 dispatch branch the base address advances in BF16 elements *before* the cast, then independent lanes store quantized FP8 values. The transfer copies one byte per hidden component. The host slices the received BF16 tensor, reshapes and concatenates the packed data as BF16 elements. The dequantizer subsequently reads that BF16 tensor through the FP8 pointer and numerically converts the loaded values to FP32 and then BF16. This exposes both typed views of the transported payload. It does not imply BF16 arithmetic on the packed values. [Buffer and parameters](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/tutorials/04-deepseek-infer-all2all.py#L461-L465) · [Allocation](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/tutorials/04-deepseek-infer-all2all.py#L515-L520) · [Base and FP8 writes](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/tutorials/04-deepseek-infer-all2all.py#L168-L215) · [Byte count](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/tutorials/04-deepseek-infer-all2all.py#L233-L239) · [Dispatch and packed host transport](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/tutorials/04-deepseek-infer-all2all.py#L550-L603) · [Dequant load](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/tutorials/04-deepseek-infer-all2all.py#L387-L405)

**T04 reference.** The reference allocates an empty BF16 tensor of shape `(m, N // 2)`. Its first payload write is FP8, at line 363. The dequantizer called directly on that output doubles the supplied width and reads FP8 at line 397. The reference path therefore contains a changed pointer type and packed layout, but no intervening BF16 payload read or write is shown. Category I here describes the writer/reader pair. It does not establish normalization to offsets in the original BF16 array: odd FP8 lanes would require half a BF16 element. For all twelve T04 sites, divisibility by the *actual* FP8 load/store width holds. Divisibility by two is a different claim: the tutorial enforces `HIDDEN % 128 == 0`, and uses four groups of 128 for the increments. Column offsets range over consecutive bytes. The generic helpers alone do not establish even row strides for arbitrary `N`. [Reference allocation and launches](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/tutorials/04-deepseek-infer-all2all.py#L410-L429) · [Reference caller](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/tutorials/04-deepseek-infer-all2all.py#L626-L631) · [Column indices](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/tutorials/04-deepseek-infer-all2all.py#L343-L355)

## Reached CUDA front-end wrappers

These rows are additional source sites below the kernel call surface. NV denotes the pinned Python NVSHMEM adapter, LE the pinned CUDA language extras. Every NV row explicitly passes `_semantic=_semantic`. It threads the front-end context; no additional value or memory effect is attributed to that keyword. Scalar rows give the destination specified in the adapter and identify a source type when fixed by the caller; rank, size and signal-value arguments can be runtime operands or compile-time constants. Their exact source widths are not specified universally. The public API distinguishes numeric conversion from `bitcast=True`. The pinned definition reads `def cast(input, dtype: dtype, fp_downcast_rounding: Optional[str] = None, bitcast: bool = False, _semantic=None):`. The parameter documentation supplies no user-level meaning for the context. [Triton cast API, accessed 2026-11-23](https://triton-lang.org/main/python-api/generated/triton.language.cast.html) · [Pinned Triton cast signature](https://github.com/triton-lang/triton/blob/f797708c0626e5f9840ca5b0a98790e2c7cb09ad/python/triton/language/core.py#L1997) · [Pinned wrapper caller, put](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/language/extra/cuda/libnvshmem_device.py#L443-L453) · [Pinned wrapper caller, put with signal](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/language/extra/cuda/libnvshmem_device.py#L525-L535)

| Site | Operand and before → after | Added byte offset / final access | Classification |
| --- | --- | --- | --- |
| [NV:429](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/language/extra/cuda/libnvshmem_device.py#L429) | `dest`, caller element pointer → void pointer | 0; ordinary put transfers the caller’s byte count. No void element load/store. | I for this conversion. The ABI copy carries the caller’s bytes. |
| [NV:430](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/language/extra/cuda/libnvshmem_device.py#L430) | `source`, caller element pointer → void pointer | 0; ordinary put transfers the caller’s byte count. No void element load/store. | I for this conversion. The ABI copy carries the caller’s bytes. |
| [NV:483](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/language/extra/cuda/libnvshmem_device.py#L483) | `dest`, caller element pointer → void pointer | 0; signalling put transfers the caller’s byte count. No void element load/store. | I for this conversion. The ABI copy carries the caller’s bytes. |
| [NV:484](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/language/extra/cuda/libnvshmem_device.py#L484) | `source`, caller element pointer → void pointer | 0; signalling put transfers the caller’s byte count. No void element load/store. | I for this conversion. The ABI copy carries the caller’s bytes. |
| [NV:431](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/language/extra/cuda/libnvshmem_device.py#L431) | `nbytes`, caller integer → uint64 | Scalar; no address or memory read. | Value conversion. |
| [NV:432](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/language/extra/cuda/libnvshmem_device.py#L432) | `pe`, caller integer → int32 | Scalar; no address or memory read. | Value conversion. |
| [NV:485](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/language/extra/cuda/libnvshmem_device.py#L485) | `nbytes`, caller integer → uint64 | Scalar; no address or memory read. | Value conversion. |
| [NV:487](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/language/extra/cuda/libnvshmem_device.py#L487) | `signal`, caller integer → uint64 | Scalar; no address or memory read. | Value conversion. |
| [NV:488](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/language/extra/cuda/libnvshmem_device.py#L488) | `sig_op`, caller integer → int32 | Scalar; no address or memory read. | Value conversion. |
| [NV:489](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/language/extra/cuda/libnvshmem_device.py#L489) | `pe`, caller integer → int32 | Scalar; no address or memory read. | Value conversion. |
| [NV:556](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/language/extra/cuda/libnvshmem_device.py#L556) | `signal`, caller integer → uint64 | Scalar; no address or memory read. | Value conversion. |
| [NV:557](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/language/extra/cuda/libnvshmem_device.py#L557) | `sig_op`, caller integer → int32 | Scalar; no address or memory read. | Value conversion. |
| [NV:558](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/language/extra/cuda/libnvshmem_device.py#L558) | `pe`, caller integer → int32 | Scalar; no address or memory read. | Value conversion. |
| [NV:580](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/language/extra/cuda/libnvshmem_device.py#L580) | `cmp_`, caller integer → int32 | Scalar; no address or memory read. | Value conversion. |
| [NV:581](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/language/extra/cuda/libnvshmem_device.py#L581) | `cmp_val`, caller integer → uint64 | Scalar; no address or memory read. | Value conversion. |
| [NV:486](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/language/extra/cuda/libnvshmem_device.py#L486) | uint64 pointer required at NV:478 → uint64 pointer | 0; 8-byte word, same width. Absolute alignment needs a valid word pointer. | I on the admitted path. |
| [NV:555](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/language/extra/cuda/libnvshmem_device.py#L555) | uint64 pointer required at NV:550 → uint64 pointer | 0; 8-byte word, same width. Absolute alignment needs a valid word pointer. | I on the admitted path. |
| [NV:579](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/language/extra/cuda/libnvshmem_device.py#L579) | int64 or uint64 pointer admitted at NV:573 → uint64 pointer | 0; 8-byte word, same width. Absolute alignment needs a valid word pointer. | II for int64 storage: read the signed cell, then compare its 64 bits as unsigned. I for uint64 storage. |
| [LE:700](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/language/extra/cuda/language_extra.py#L700) | Inside `st` (CO:177). `_semantic=`. | — | III. Inline-assembly function; stop at this boundary. |
| [LE:702](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/language/extra/cuda/language_extra.py#L702) | Inside `st` (CO:177). `bitcast=True` and `_semantic=`. | — | III. Inline-assembly function; stop at this boundary. |
| [LE:703](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/language/extra/cuda/language_extra.py#L703) | Inside `st` (CO:177). `_semantic=`. | — | III. Inline-assembly function; stop at this boundary. |
| [LE:711](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/language/extra/cuda/language_extra.py#L711) | Inside `st` (CO:177). `_semantic=`. | — | III. Inline-assembly function; stop at this boundary. |
| [LE:713](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/language/extra/cuda/language_extra.py#L713) | Inside `st` (CO:177). `_semantic=`. | — | III. Inline-assembly function; stop at this boundary. |

The signal casts use `pi_u64_t` defined at NV:31. The tutorial signal dtype is `torch.int64`; T03 and T04 allocate signal tensors in that dtype. NV:573 accepts a signed word and reads it as unsigned. NV:478 and NV:550 assert an unsigned pointer before their casts. Tutorial 03 calls `putmem_signal_block`, and its harness allocates signals with `NVSHMEM_SIGNAL_DTYPE` (int64). All four tests in the single-host batch `internode-logical-ag03-001` returned `ok`, so the tested kernels compiled and ran. The inspected source does not establish how the signed allocation passes the unsigned-pointer check. Runtime lowering, absolute addresses and external library implementations remain unchecked. [T03 call](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/tutorials/03-inter-node-allgather.py#L85-L92) · [Harness allocation](../../experiments/interp_gpu/internode_logical/harness.py#L131) · [GPU results](../GpuInterNodeRuns.md#the-tutorial-requests) · [Alias](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/language/extra/cuda/libnvshmem_device.py#L29-L32) · [Signal dtype](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/utils.py#L572) · [T03 signal allocation](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/tutorials/03-inter-node-allgather.py#L271-L278) · [T04 signal allocation](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/tutorials/04-deepseek-infer-all2all.py#L523-L528) · [Wait signature](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/language/extra/cuda/libnvshmem_device.py#L572-L581)

## Kernel-level pointer views

The public `with_pointer_views launch in triton { … }` quotation projects the address operations of one active lane to ranges of `Dist.Addr` cells. A launch supplies each pointer's physical space, region, base byte address, extent, declared pointee and actual access unit. Different names for a physical allocation must have consistent allocation metadata. Integer-to-pointer conversion requires exactly one in-bounds allocation for the address. The caller supplies valid allocation provenance, valid ranks, the active lane indices and the specialized device path. Source index arithmetic must stay representable in its source integer type. Buffer declarations describe the actual allocations. Symmetric peers must provide matching extents and cell units for the transferred region. The adapter checks that distinct physical allocations in one address space have disjoint byte ranges. The result contains reads, writes and the two cell ranges of each put/get, with the remote range projected via `symmAt`. [Adapter](../../VeriTile/Dist/Frontend/TritonExt/PointerCasts.lean) · [Public-entrypoint regressions](../../tests/lean/dist/PointerCasts.lean)

A pointer increment scales its signed index by the byte width of its current pointee. A cast preserves that relative byte displacement. Widening requires an aligned allocation address and a displacement divisible by the new width. Thus advancing two BF16 elements, casting to FP8 and advancing three lanes selects FP8 cell seven. Every typed load or store must match the allocation’s cell dtype, as required by `MemCell.readAs`. The check also applies after a void cast, conversion from an integer address or a mismatched argument declaration. A transfer requires the same cell dtype at both endpoints and checks the start, length and extent of each range. Equal byte counts then select equal numbers of cells. T04 online dispatch binds the receive slab to FP8 for its put, and combine binds the corresponding endpoints to BF16. An ABI void pointer can participate in a transfer. Dereferencing it fails. For scalar values, the ordinary `triton` compute frontend retains the distinction between numeric `tl.cast`/`.to` and `bitcast=True`; its existing bit-pattern rules apply. Importing the adapter registers its value-cast elaborator on ordinary `triton` blocks, where it delegates normalized syntax to the compute frontend.

**T04 host contract for #155/#156.** Device code may change the unit across launches only if it never reads the previous contents through the new unit. The reference quantizer writes FP8 and the next kernel reads FP8. The online dequantizer reads the host-supplied FP8 rows and writes a fresh BF16 output. Combine reads that fresh output, writes BF16 to the reused receive slab and transfers only the rows it just wrote. The host must gather whole FP8 token rows **byte-exactly and in order**, using offsets and lengths divisible by the narrower unit. `reshape(-1, N // 2)` exposes one N-byte row of BF16 containers; the slice beginning at `off * 2` is row-aligned. This arithmetic and the pinned call chain are checked independently of the host's bit-preserving behavior. VeriTile takes that behavior as a premise. A future end-to-end theorem may require the deferred byte representation. [T04 host and kernel decisions](https://github.com/VeriInfra-Lab/VeriTile-2/issues/548#issuecomment-7146151459) · [Kernel contract #156](https://github.com/VeriInfra-Lab/VeriTile-2/issues/156) · [Pinned-source checks](../../scripts/census/test_t04_pointer_contract.py)

### Step 2 site dispositions

The following rows refer to the individual source links in the inventory above. Coverage is for the address expression of an active lane, instantiated with the caller's indices and allocation. An external library call, kernel schedule and host implementation remain separate obligations.

| Sites | Count | Kernel-level disposition |
| --- | ---: | --- |
| T03:86 destination cast and add; T03:88 source cast and add | 4 | Covered. Casting the int8 pointer preserves its displacement; adding the segment offset selects that many cells. |
| T03:132 rebinding; T03:140 destination; T03:141 source; T03:170 destination; T03:171 source | 5 | Covered. Rebinding and all four additions retain the physical allocation and int8 unit. |
| T04:192 dispatch cast and add; T04:212 inner advance; T04:215 outer advance | 4 | Covered. A BF16 base advance scales by two before the cast; the group offset and subsequent increments count FP8 cells, including odd lanes. |
| T04:350 reference output cast, row add and column add; T04:370 output advance | 4 | Covered. FP8 writes use the cast base, row stride, column lane and four-group increment. |
| T04:387 dequant input cast, row add and column add; T04:405 input advance | 4 | Covered. FP8 reads use those same address operations. Online data requires the host contract above. |
| NV:429 destination, NV:430 source; NV:483 destination, NV:484 source | 4 | Covered. Each endpoint casts to void with the forwarded `_semantic` context and retains its allocation and byte displacement for the transfer. Signal effects of the external call are outside this address projection. |
| NV:486 and NV:555, both unsigned signal-address identities | 2 | Covered on the wrappers' checked `pi_u64_t` inputs. Both retain the uint64 pointer and word alignment. |
| **In scope** | **27** | **27 covered under the stated preconditions.** |

NV:579 is one additional value-level site (#549). `libshmem_device.signal_wait_until` accepts an aligned int64 or uint64 pointer to one in-bounds word. The projection preserves its physical address and actual storage type. `SignalWait.observe` takes the authoritative cell map (`DistState.cell`), reads that address as its stored type and checks that the value fits the declared 64 bits. For signed storage, two’s complement maps −1 to 18,446,744,073,709,551,615; the resulting word also recovers −1 via `BitVec.toInt`. The wait compares its unsigned word with the caller’s integer converted to uint64 (NV:581), using the source comparator and `Cmp.holds`. Source comparison targets span −2^63 through 2^64−1 inclusive. Outside that interval projection returns `signal wait: target outside int64 and uint64 ranges` (#592). A satisfied observation returns the word; an unsatisfied one remains blocked. A mismatched cell tag or unrepresentable stored value produces a diagnostic. This observation describes one memory snapshot. Scheduling and eventual progress belong to the distributed semantics. [Wait wrapper](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/language/extra/cuda/libnvshmem_device.py#L572-L592) · [T03 caller](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/tutorials/03-inter-node-allgather.py#L72-L76)

The single-lane view of `putmem_signal_block` and `putmem_signal_nbi_block` carries the copy's local source range, remote destination range and one remote signal word in the same access. Both remote endpoints use the call's peer. The access retains whether the call is nonblocking. At transfer completion, `SignalWrite.commit` applies SET or ADD to that word in the supplied distributed state. SET overwrites the cell. ADD reads the old cell at its physical dtype and adds modulo 2^64. The result has the physical tag: `.int bits.toInt` for int64 storage or `.nat bits.toNat` for uint64. Other storage types fail projection. Completion ordering and payload execution remain part of the distributed semantics. [T03 blocking site](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/tutorials/03-inter-node-allgather.py#L82-L94) · [NBI site](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/tutorials/03-inter-node-allgather.py#L139-L147)

The physical storage and the extern pointer type are separate inputs. T03 allocates its flags with `NVSHMEM_SIGNAL_DTYPE`, defined as `torch.int64`, while the CUDA put wrapper asserts a uint64 pointer and casts the operand to uint64. The adapter accepts an int64 word view or a uint64 ABI view of that same aligned physical allocation. Its round-trip tests model the stored bits at a supplied in-bounds segment. [T03 allocation](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/tutorials/03-inter-node-allgather.py#L274-L279) · [Storage dtype](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/utils.py#L572) · [CUDA put wrapper](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/language/extra/cuda/libnvshmem_device.py#L476-L494)

The five inline-assembly sites and eleven scalar keyword sites remain outside the site total. An unsupported source expression, unknown pointer provenance, mismatched cell dtypes, overlapping allocations or failed divisibility check yields a diagnostic.

## Remaining-target inventory: P2P reads (#593, partial)

The two branches of `CommOp.read` select different kernels. The `fused=True` branch dispatches current root 57, `p2p_copy_remote_to_local_kernel` (historical 98). Its status is **rejected with diagnostic, owned by #596, out of scope of #296**. The `fused=False` branch dispatches current root 55, `p2p_copy_kernel` (historical 96), then copies the synchronized communication buffer into the typed output. The table records all three root-55 and ten root-57 kernel-level source sites using the counting rule above. `begin = pid × ceil(nbytes / NUM_SMS)`. [Dispatch and typed copy](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/layers/nvidia/p2p.py#L97-L116) · [Public target numbers](../census/MinimalSyntax.md#triton-distributed) · [Coordinator’s root-57 decision](https://github.com/VeriInfra-Lab/VeriTile-2/issues/593#issuecomment-7174675011)

| Site | Root and operation | Before → after | Byte displacement | Adapter disposition and evidence |
| --- | --- | --- | --- | --- |
| [P2P:71](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/kernels/nvidia/p2p.py#L71) | 55, source cast | BF16 → int8 pointer | 0 | Accepted address view. |
| [P2P:81](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/kernels/nvidia/p2p.py#L81) | 55, get destination | int8 pointer, BF16 storage | begin | Accepted on a complete-cell interval; split case below. |
| [P2P:82](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/kernels/nvidia/p2p.py#L82) | 55, get source on peer | int8 pointer, BF16 storage | begin | Same start, size and diagnostics as the destination. |
| [P2P:127](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/kernels/nvidia/p2p.py#L127) | 57, source cast | BF16 → int8 pointer | 0 | Cast accepted; the active byte load is rejected on BF16 storage. |
| [P2P:128](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/kernels/nvidia/p2p.py#L128) | 57, destination cast | BF16 → int8 pointer | 0 | Cast accepted; the active byte store is rejected on BF16 storage. |
| [P2P:138](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/kernels/nvidia/p2p.py#L138) | 57, blocking get destination | int8 pointer, BF16 storage | begin | Accepted for the one-BF16, one-CTA full-cell control. |
| [P2P:139](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/kernels/nvidia/p2p.py#L139) | 57, blocking get source on peer | int8 pointer, BF16 storage | begin | Same whole-cell interval as the destination. |
| [P2P:147](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/kernels/nvidia/p2p.py#L147) | 57, source load, chunk addition | int8 pointer, BF16 storage | begin | Address arithmetic stays in bytes. |
| [P2P:147](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/kernels/nvidia/p2p.py#L147) | 57, source load, iteration addition | int8 pointer, BF16 storage | begin + i × BLOCK_SIZE | Address arithmetic stays in bytes. |
| [P2P:147](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/kernels/nvidia/p2p.py#L147) | 57, source load, lane addition | int8 pointer, BF16 storage | begin + i × BLOCK_SIZE + offs | Active byte access requires a BF16/byte relation; #596. |
| [P2P:149](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/kernels/nvidia/p2p.py#L149) | 57, destination store, chunk addition | int8 pointer, BF16 storage | begin | Address arithmetic stays in bytes. |
| [P2P:149](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/kernels/nvidia/p2p.py#L149) | 57, destination store, iteration addition | int8 pointer, BF16 storage | begin + i × BLOCK_SIZE | Address arithmetic stays in bytes. |
| [P2P:149](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/kernels/nvidia/p2p.py#L149) | 57, destination store, lane addition | int8 pointer, BF16 storage | begin + i × BLOCK_SIZE + offs | Active byte access requires a BF16/byte relation; #596. |

**Fused control, root 57.** A one-CTA get of one BF16 copies one whole cell. The subsequent active int8 payload load and store cannot observe or update separate bytes of BF16 storage in D. The first access returns `pointer view: mixed access widths or incorrect launch unit for this buffer`. Choosing int8 storage produces two get cells and a one-byte read/write footprint, without relating that state to the BF16 input or output. The published test selects the non-fused branch. The fused Lean client specializes the address operations to iteration 0, lane 0 and one CTA of a one-BF16 launch that the public API permits. All six address additions at P2P:147 and P2P:149 are classified from the pinned source. The Lean client uses the resulting zero-offset addresses directly and does not exercise those six expressions. [Fused kernel](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/kernels/nvidia/p2p.py#L119-L150) · [Gated public adapter clients](../../tests/lean/dist/P2PTransferViews.lean)

**Non-fused, root 55.** The caller selects the symmetric BF16 allocation, fills it with a nonuniform tensor on the sending rank, reads it with `fused=False`, and checks the received typed result. At the pinned test defaults (8192 × 6144 BF16, eight CTAs), 100663296 bytes divide into eight 12582912-byte gets. All starts and lengths are even. D gives 6291456 BF16 cells per CTA. Changing only the public `--num_sms` option to 7 produces a 14380471-byte first chunk. CTA 0 copies through byte 14380470 inclusive, the first byte of BF16 cell 7190235; CTA 1 starts at byte 14380471, the second byte of that cell. CTA 0 returns `pointer view: byte count is not divisible by the buffer unit`; CTA 1 returns `pointer view: transfer start is not cell aligned`. The public Lean test calculates the CTA partition in Lean and supplies the start and size as launch integers to the adapter. It checks both diagnostics and the last default CTA's successful range. Each tested start is within the allocation, so the test does not exercise negative remaining lengths. [Command-line controls](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/test/nvidia/test_pp.py#L38-L47) · [BF16 input and allocation](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/test/nvidia/test_pp.py#L232-L260) · [Producer](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/test/nvidia/test_pp.py#L82-L94) · [Non-fused receiver](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/test/nvidia/test_pp.py#L127-L143) · [Typed comparison](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/test/nvidia/test_pp.py#L284-L295) · [CTA partition and get](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/kernels/nvidia/p2p.py#L66-L85)

A minimal witness uses one BF16 and two CTAs. They copy bytes [0,1) and [1,2) from the same peer to the corresponding offsets in local storage. After just one get the local BF16 may contain one byte from each rank. Modelling each individual transfer against populated BF16 storage needs a relation for a partial-cell update. An int8-unit control accepts both footprints and leaves this relation open. Unlike root 57, the kernel itself only issues a blocking get. For a whole-launch specification the two byte ranges cover the original word, independently of byte order; grouping the gets would require its own contract and proof of when the partially updated word is observable. This inventory establishes the source path and exact D diagnostics using Lean; it did not run a GPU transfer. [Public adapter controls](../../tests/lean/dist/P2PTransferViews.lean) · [Runtime validation in the pinned client](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/layers/nvidia/p2p.py#L101-L116)

The new root-55 split-cell case awaits a scope decision under #593. Of the 14 current roots, these two P2P reads have the kernel-site dispositions above. The one allreduce, five common_ops, one P2P put, two T03 and three T04 roots still await the complete remaining-target reconciliation (the step-1 tutorial evidence below remains available). The 18 retired roots comprise four ep_all2all_fused, two low_latency_all_to_all_v2 and twelve low_latency_allgather roots. They are retired, not classified; retired root 80 → helper 75 is separately owned by #596. The 14-root scanner count, the reached `getmem_block` → `_getmem_impl` wrapper sites and the 18 retired roots as individual source-path/kernel-name rows remain open. [Continuation decision](https://github.com/VeriInfra-Lab/VeriTile-2/issues/593#issuecomment-7169031258)

## Coverage and totals

| Inventory covered | Kernel casts | Kernel pointer arithmetic | Reached wrapper sites | Total distinct sites |
| --- | ---: | ---: | ---: | ---: |
| #448 step 1 | 6 | 15 | 23 | 44 |
| #593 P2P read roots 55 and 57, kernel sites only | 3 | 10 | — | 13 |
| **Recorded across both inventories** | **9** | **25** | **23** | **57** |

The interpretation categories below apply to the original step-1 sites.

| Counted source surface | I: same payload interpretation | II: different typed views | III: inline assembly | Scalar keyword conversion | Total |
| --- | ---: | ---: | ---: | ---: | ---: |
| Kernel cast expressions | 4 | 2 | 0 | 0 | 6 |
| Kernel pointer arithmetic | 9 | 6 | 0 | 0 | 15 |
| Reached CUDA primitive wrappers | 6 | 1 | 5 | 11 | 23 |
| **Total distinct sites** | **19** | **9** | **5** | **11** | **44** |

II takes precedence when an expression serves both paths. Four of the thirteen kernel I sites belong to the packed FP8 reference output and nine to int8 byte copies. In particular, simply equating “allocated as BF16” with “payload produced as BF16” would change the count. Five III rows identify source locations only. The eleven additional scalar casts are counted for their keyword, separately from pointer operations. The reached sites contain no `dtype=` keyword of `tl.cast`; passing a dtype positionally and using `dtype=` on a different API are distinct. No `.to(tl.pointer_type(...))` occurs in the step-1 kernel set. All three P2P read casts use this spelling.

The eight tutorial files contain qualifying kernel expressions only in T03 and T04. Following the seven library kernels in the call graph adds no direct kernel sites. CO:73,76,105,122,125 occur in other grid-barrier helpers; those helpers and the separate low-latency/EP K-M sources belong to the wider parent census. On the reached K16 scalar `st` path, the vector overload at LE:695–696 is not selected. The DeepEP directory contains `get_dispatch_layout.py`, `dispatch.py`, `combine.py`, `example_intranode.py`, and `test_intranode.py`. Its seven kernels use TileScale. None of the five files contains the requested Triton pointer or keyword forms; `T.cast(idx_value, "int32")` in dispatch is a scalar TileScale expression. [Reachable versus unused kernels](EventControlFlow.md#2-sources) · [Wider grid helper](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/kernels/nvidia/common_ops.py#L61-L142) · [Scalar source call](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/kernels/nvidia/common_ops.py#L172-L179) · [DeepEP scalar cast](https://github.com/tile-ai/tilescale/blob/9ba8a605d347f600a95d0275e2639cb00122c084/examples/distributed/deepseek_deepep/intranode/dispatch.py#L385)

### Reproducing the source counts

With the checkout directories of the two pins in `TD` and `TS`, run the following with Python 3.10 or later from the VeriTile root. The scanner reads Python syntax without importing either project. It follows assigned cast pointers and increments inside each function, resets a pointer overwritten in a different branch, and prints distinct casts, arithmetic expressions and source wrapper keywords. The scanner uses source positions internally to distinguish nested additions. Its table check compares the number of occurrences for each (file alias, line) pair. The check does not compare columns, operator text or classifications.

```python
import ast
import os
import re
from collections import Counter
from pathlib import Path

td, ts = Path(os.environ["TD"]), Path(os.environ["TS"])
base = td / "python/triton_dist"
nv = base / "kernels/nvidia"
cuda = base / "language/extra/cuda"
files = {f: None for f in sorted((td / "tutorials").glob("0[1-8]-*.py"))}
assert len(files) == 8
files[nv / "p2p.py"] = {"p2p_copy_kernel", "p2p_copy_remote_to_local_kernel"}
files[nv / "common_ops.py"] = {
    "barrier_all_intra_node_atomic_cas_block", "barrier_all_intra_node_non_atomic_block",
    "_barrier_all_intra_node_non_atomic_once_block",
}
files[nv / "reduce_scatter.py"] = {
    "kernel_ring_reduce_tma", "kernel_ring_reduce_non_tma",
    "kernel_inter_node_p2p_for_same_local_rank", "add_continuous_kernel",
}
files[cuda / "libnvshmem_device.py"] = {
    "_putmem_impl", "_putmem_signal_impl", "signal_op", "signal_wait_until",
    "putmem_block", "putmem_nbi_block", "putmem_signal_block", "putmem_signal_nbi_block",
    "fence", "barrier_all_block", "_barrier_all_impl",
}
files[cuda / "language_extra.py"] = {"st", "ld", "atomic_cas", "atomic_add", "__syncthreads", "tid"}
port = ts / "examples/distributed/deepseek_deepep/intranode"
deep = sorted(port.glob("*.py"))
assert len(deep) == 5
files.update({f: None for f in deep})
seen = set()

def expr(node, live):
    if isinstance(node, ast.Name):
        return node.id in live
    children = [expr(child, live) for child in ast.iter_child_nodes(node)]
    kind, pointer = None, False
    if isinstance(node, ast.Call):
        name = ast.unparse(node.func)
        has_ptr = any(isinstance(x, ast.Call) and ast.unparse(x.func) == "tl.pointer_type"
                      for x in node.args + [k.value for k in node.keywords])
        keywords = {k.arg for k in node.keywords}
        pointer = has_ptr and (name == "tl.cast" or name.endswith(".to"))
        if pointer or (name == "tl.cast" and keywords & {"dtype", "bitcast", "_semantic"}):
            kind = "cast"
    elif isinstance(node, ast.BinOp) and isinstance(node.op, (ast.Add, ast.Sub)):
        pointer = any(children)
        if pointer:
            kind = "arithmetic"
    if kind:
        seen.add((f.name, node.lineno, node.col_offset, node.end_lineno, node.end_col_offset, kind))
    return pointer

def statements(body, live):
    for st in body:
        if isinstance(st, ast.Assign):
            pointer = expr(st.value, live)
            for t in st.targets:
                if isinstance(t, ast.Name):
                    if pointer:
                        live.add(t.id)
                    else:
                        live.discard(t.id)
        elif isinstance(st, ast.AugAssign):
            if isinstance(st.target, ast.Name) and st.target.id in live:
                seen.add((f.name, st.lineno, st.col_offset, st.end_lineno, st.end_col_offset, "arithmetic"))
            expr(st.value, live)
        elif isinstance(st, (ast.If, ast.For, ast.While)):
            expr(st.iter if isinstance(st, ast.For) else st.test, live)
            branches = [statements(b, live.copy()) for b in (st.body, st.orelse)]
            live = branches[0] | branches[1]
        elif not isinstance(st, (ast.FunctionDef, ast.AsyncFunctionDef)):
            expr(st, live)
    return live

for f, names in files.items():
    tree = ast.parse(f.read_text())
    funcs = [fn for fn in ast.walk(tree) if isinstance(fn, ast.FunctionDef)]
    if names:
        assert names <= {fn.name for fn in funcs}, f
    for fn in funcs:
        if names is None or fn.name in names:
            statements(fn.body, set())
    if f in deep:
        statements(tree.body, set())
for row in sorted(seen):
    print(*row)
counts = Counter((file, kind) for file, *_, kind in seen)
assert counts == {
    ("p2p.py", "cast"): 3, ("p2p.py", "arithmetic"): 10,
    ("03-inter-node-allgather.py", "cast"): 3, ("03-inter-node-allgather.py", "arithmetic"): 6,
    ("04-deepseek-infer-all2all.py", "cast"): 3, ("04-deepseek-infer-all2all.py", "arithmetic"): 9,
    ("libnvshmem_device.py", "cast"): 18, ("language_extra.py", "cast"): 5,
}, counts
aliases = {
    "p2p.py": "P2P",
    "03-inter-node-allgather.py": "T03", "04-deepseek-infer-all2all.py": "T04",
    "libnvshmem_device.py": "NV", "language_extra.py": "LE",
}
expected = Counter((aliases[file], line) for file, line, *_ in seen)
table = Path("documents/dist/PointerCasts.md").read_text()
listed = Counter((name, int(line)) for name, line in
                 re.findall(r"^\| \[(T03|T04|NV|LE|P2P):(\d+)\]", table, re.MULTILINE))
assert listed == expected, (listed - expected, expected - listed)
```
