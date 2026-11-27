# DeepEP v1 CTA combine variant

The [#636 decision](https://github.com/VeriInfra-Lab/VeriTile-2/issues/636#issuecomment-7206156826) selects an int32 retirement flag and block-scoped release/acquire accesses for the three shared arrays in K28. Apply [combine-cta.patch](combine-cta.patch) after the seven-site [dispatch variant](DispatchVariant.md). The first GPU request retains its own entry and patch.

| TileScale `9ba8a605` combine.py lines | Object | Operation in the variant |
| --- | --- | --- |
| 230, 232 | `warp_retired` | Allocate int32 and initialize each entry to 0. All three arrays retain their ordinary initialization before the original block barrier at 237. |
| 247, 261 | `warp_retired[i]` | Acquire an int32 into a local, then test nonzero/zero for the original predicates. |
| 262 | `warp_channel_head_idx[i, lane_id]` | Acquire the head before taking its minimum. |
| 255, 284, 286 | `shared_channel_tail_idx[lane_id]` | The pinned original already uses a CTA release and two CTA acquires here. |
| 343–345 | `warp_channel_head_idx[warp_id, lane_id]` | Release the original index expression. |
| 350 | `warp_retired[warp_id]` | Release int32 value 1. |
| 265 | `channel_head_idx` in global memory | Inherit the dispatch stage's system-scope release. |

## Compilation and address spaces

The [saved CUDA](combine-cta.cu) is the byte-for-byte output of full TileScale device compilation at the same pin, compiler, pass configuration and parameters as the first stage. SHA-256 is `efd51079bc674e76309fde260b6e8a1d11bad122e057cad72cec023de283460f`. The generated kernel declares three `__shared__ int` arrays of 24, 48 and 32 entries. Its eight explicit synchronization sites comprise five CTA acquire loads and three CTA release stores.

```sh
area=experiments/interp_gpu/deepep_v1
python3 "$area/dispatch_variant.py" materialize "$TILESCALE_CHECKOUT" "$WORK/ports-cta" --combine
export CUDA_VISIBLE_DEVICES= TILELANG_USE_DISTRIBUTED=1
python3 "$area/dispatch_variant.py" compile "$WORK/ports-cta/combine-cta" combine_kernel "$WORK/combine-cta.cu"
cmp "$area/combine-cta.cu" "$WORK/combine-cta.cu"
nvcc -std=c++17 -arch=sm_90a -I "$TILESCALE_CHECKOUT/src" -I "$TILESCALE_CHECKOUT/3rdparty/cutlass/include" \
    --ptx "$WORK/combine-cta.cu" -o "$WORK/combine-cta.ptx"
```

At nvcc 12.8.61 the emitted PTX declares 96, 192 and 128 bytes in `.shared`, converts the shared symbols to generic pointers with `cvta.shared.u64`, and uses `ld.acquire.cta.b32` (71 static instances after unrolling) and `st.release.cta.b32` (three). An omitted state-space qualifier uses generic addressing, so the shared address selects shared storage. The `.cta` suffix specifies synchronization scope. [PTX ISA 8.7, Generic Addressing](https://docs.nvidia.com/cuda/archive/12.8.1/parallel-thread-execution/index.html#generic-addressing)

On the same pin, the GPU-scope specializations explicitly append `.gpu.global` for release and acquire. This selects global storage for an address obtained from a shared object, which lies outside the instruction's declared state space. Compilation alone could accept those inline instruction strings. This is a source- and ISA-level diagnosis. No invalid access was launched, and no hardware fault behavior is inferred. [Pinned store and load specializations](https://github.com/tile-ai/tilescale/blob/9ba8a605d347f600a95d0275e2639cb00122c084/src/tl_templates/cuda/ldst.h#L171-L212), [PTX ISA 8.7, State Spaces](https://docs.nvidia.com/cuda/archive/12.8.1/parallel-thread-execution/index.html#state-spaces)

The [A11 record](../../../documents/dist/PrimitiveSources.md#a11-deepep_v1_cta_scope_is_block) supplies the source-side scope assumption for this pinned port. The compiler observations above are available for the coordinator's upstream-observation decision. DRF and whole-kernel correctness remain proof work.

## GPU comparison

The [combined request](../batches/deepep-v1-variant-intranode-002/batch.json) uses the same original cases. Its entry applies both patches in each fresh rank process. The GPU operator runs this request after the dispatch-first handback. Judge the returned complete bundle with the same recorded 36 output files and their repeat counts.

```sh
python3 experiments/interp_gpu/deepep_v1/judge_variant.py "$VARIANT_RESULT_BUNDLE" --batch deepep-v1-variant-intranode-002
```
