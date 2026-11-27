# DeepEP v1 dispatch variant

The first GPU comparison for [#636](https://github.com/VeriInfra-Lab/VeriTile-2/issues/636#issuecomment-7206156826) runs the original two-rank layout, dispatch and combine harness with seven changed sites. The original is [TileScale at 9ba8a605](https://github.com/tile-ai/tilescale/tree/9ba8a605d347f600a95d0275e2639cb00122c084/examples/distributed/deepseek_deepep). [The patch](dispatch-release.patch) retains the original lines next to their replacements. All three head stores address system-scope counters. The corresponding upstream relaxed stores are recorded in the issue.

| Pinned file | Lines | Change |
| --- | --- | --- |
| `intranode/dispatch.py` | 432, 434 | Add system scope to the volatile start and end offset loads |
| `intranode/dispatch.py` | 511 | Publish the ordinary dispatch head with release |
| `intranode/dispatch.py` | 674, 676 | Add system scope to the cached dispatch offset loads |
| `intranode/dispatch.py` | 740 | Publish the cached dispatch head with release |
| `intranode/combine.py` | 265 | Publish the combine head with release |

Use the editable TileScale checkout from the pinned experiment environment. The materializer checks its Git revision and reads the original port from tracked Git objects. It creates two sibling directories under a fresh destination. The rank entry uses a private copy for its lifetime. The startup check rejects processes that previously imported a DeepEP port.

```sh
area=experiments/interp_gpu/deepep_v1
python3 "$area/dispatch_variant.py" materialize "$TILESCALE_CHECKOUT" "$WORK/ports"
export CUDA_VISIBLE_DEVICES= TILELANG_USE_DISTRIBUTED=1
for k in dispatch_kernel cached_dispatch_kernel combine_kernel; do
  python3 "$area/dispatch_variant.py" compile "$WORK/ports/dispatch-release" "$k" "$WORK/$k.cu"
done
```

Each invocation requests the full TileScale device compilation at Hopper SM90a with the kernel's own pass configuration. The explicit parameters correspond to the recorded 2-rank run with 40 tokens per rank, hidden dimension 64, top-k 2, 8 experts and 20 SMs. The cached dispatch kernel is covered by compilation as an additional path. The GPU harness follows the original uncached dispatch sequence.

The author compiled all three kernels without a visible device using TileScale `0.1.7.post1+cuda.git9ba8a605`, its TVM and TVM-FFI submodule revisions, PyTorch `2.9.1+cu126` and nvcc `12.8.61`. Each emitted file also compiled independently with `nvcc -std=c++17 -arch=sm_90a --cubin` and the pinned TileScale and CUTLASS include directories.

| Kernel | SHA-256 of generated CUDA |
| --- | --- |
| `dispatch_kernel` | `3ee2ebe2309c1fe1df076282d35f4bba0e9b320ac0607890b7d46717e7a9976d` |
| `cached_dispatch_kernel` | `236cb3987a3912226c936450d21626f44d3ea8284480e9bcb43fd4b424c0eb6d` |
| `combine_kernel` | `1dffb730f308e53ef557c04b3c2921c676616e4e4c4a50028b88de5942df37e7` |

The generated CUDA selects `VOLATILE, SYS` on the four offset reads and `RELEASE, SYS` on each head store. The [pinned instruction templates](https://github.com/tile-ai/tilescale/blob/9ba8a605d347f600a95d0275e2639cb00122c084/src/tl_templates/cuda/ldst.h#L194-L198) implement volatile system loads with `ld.volatile.global`.

## Compare on the recorded inputs

Use the [variant request](../batches/deepep-v1-variant-intranode-001/batch.json) through the project's distributed GPU runner. The original identity and rank-weighted cases, input generators and hashes, launch parameters, output schemas, two ranks and two repeats are preserved. The coordinator owns the GPU request and judgment. The ordinary path executes DD 432/434/511 and DC 265. With these inputs the head stores at DD 511 and DC 265 are never waited on (thresholds are negative). `equal` shows that the patched source compiles and completes; the memory-order change cannot be confirmed by comparing outputs. DD 674/676/740 have compilation coverage.

Each rank hashes all eight Python files in its private materialized directory before passing that directory to the origin-checked harness. The runner saves the resulting `deepep-source-sha256` JSON line in the test's `stdout.log` under its repeat header. For both repeats, the judge requires exactly one complete record per rank. The [source hash table](source-sha256.json) pins the SHA-256 of the eight original files read from Git at the TileScale revision and of the two patched files for this batch. The patched values were independently reproduced from those blobs using the seven edits listed above. Both changed file hashes must match the patched values and differ from the originals. The other six must match their originals. Missing evidence, including from an older result bundle, yields a difference.

```sh
python3 -B -m unittest discover -s experiments/interp_gpu/deepep_v1 -p 'test_*.py'
python3 experiments/interp_gpu/deepep_v1/judge_variant.py "$VARIANT_RESULT_BUNDLE"
```

The [recorded output hashes](recorded-002.json) come from [the judged #457 bundle at 017d5ca6](https://github.com/VeriInfra-Lab/VeriTile-2/tree/017d5ca63a89cf82ac575efb5cb530e50297ff40/results/deepep-v1-intranode-002). Each original rank produced a single tensor for each output digest across its two repeats. The judge reads the candidate tensor files, verifies their full-file SHA-256 and original value oracle, and checks the two occurrences of every recorded digest. This gives 36 distinct test/rank/output comparisons covering all 72 output observations, including sentinel bytes and tensor headers. Equality on these inputs is an experimental result. The combine shared-memory variant and its scoped trust assumption are a separate stage.

## Compare with head-dependent ring reuse

The [small-ring request](../batches/deepep-v1-variant-intranode-003/batch.json) uses the same two ranks, 40 input tokens per rank, 8 experts, rank weights `[1, -0.5]`, dispatch send block of 24 and combine send block of 10. It selects **2 SMs (one channel) and 24 receive slots** for both kernels through the port’s `EPBuffer` and `Config`. The rank entry logs the constructed configuration. The judge checks it for every rank and repeat, along with the dispatch-release source hashes and the original rank-weighted tensor hashes.

In batch 001, 20 SMs divide 40 tokens across 10 channels. Each channel handles at most four tokens per source/destination. Dispatch reserves a full block on its first wait (`24 − 256 = −232`). Combine reserves the actual remaining count (`1…4 − 256 = −255…−252` for a nonempty queue). Each sends at most one round. In batch 003, one channel contains all 40 source tokens. Dispatch waits for `tail + 24 − 24` before each round. Combine sends the same routed rows back and waits for `tail + min(10, remaining) − 24`. The last combine round starts at `tail = 20` for all four pairs. The table follows the generated `topk_idx` rows, counting each destination once per token. [Dispatch lines 313–359](https://github.com/tile-ai/tilescale/blob/9ba8a605d347f600a95d0275e2639cb00122c084/examples/distributed/deepseek_deepep/intranode/dispatch.py#L313-L359), [combine lines 149–180](https://github.com/tile-ai/tilescale/blob/9ba8a605d347f600a95d0275e2639cb00122c084/examples/distributed/deepseek_deepep/intranode/combine.py#L149-L180).

| Dispatch route (combine reverses it) | Rows | Positive dispatch threshold | Positive combine threshold |
| --- | ---: | ---: | ---: |
| 0 → 0 | 29 | 24 | 5 |
| 0 → 1 | 24 | none | none |
| 1 → 0 | 29 | 24 | 5 |
| 1 → 1 | 28 | 24 | 4 |

On each positive entry a sender that reaches the wait with head zero must block. Progress requires a consumer head update at DD 511 or DC 265 respectively. For the 24-row route the final selected row is input token 39, so dispatch has no further round. A GPU receiver may already have advanced before the sender's load. The thresholds establish a dependency on head publication; output equality alone does not establish the ordering of hardware memory operations.

```sh
python3 -B -m unittest discover -s experiments/interp_gpu/deepep_v1 -p test_small_ring.py -v
python3 experiments/interp_gpu/deepep_v1/judge_variant.py "$SMALL_RING_RESULT_BUNDLE" --batch deepep-v1-variant-intranode-003
```

The CPU test runs both ranks and both repeats through the ordinary bundle writer. It checks the sender-first thresholds on the regenerated routing input, all 18 rank/output digests against the recorded rank-weighted case and both repeats per digest. Configuration and source records in this CPU fixture are identified in its source. Actual GPU timing and completion belong to the coordinator’s experiment.
