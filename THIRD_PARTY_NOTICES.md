# Third-party notices

The tables use litmus filename prefixes and full paths for other files. Each identifier occurs once, under the SPDX expression in its subsection heading. We checked the pinned source paths against upstream Git trees on 2026-11-24. The offline gate checks each file against its row. The first three comments record source, licence and changes. Frozen fixtures and generated JSON carry the same three fields in adjacent `.attribution` files to preserve their byte bindings or file format.

The holder-neutral [MIT text](licenses/MIT.txt) follows [SPDX v3.26.0](https://github.com/spdx/license-list-data/blob/v3.26.0/text/MIT.txt). This repository also distributes [Apache-2.0](licenses/Apache-2.0.txt), [Apache-2.0 with LLVM exception](licenses/Apache-2.0-WITH-LLVM-exception.txt), and the BSD-3-Clause texts for [TorchAO](licenses/BSD-3-Clause-TorchAO.txt), [FlashAttention](licenses/BSD-3-Clause-FlashAttention.txt) [Random123](licenses/BSD-3-Clause-Random123.txt) and [SageAttention](licenses/BSD-3-Clause-SageAttention.txt). Each source retains its applicable copyright notice.

## Triton-distributed

[Source and licence at `7908e4ea9010bb2238f9f05b28c904fd4b71c60a`](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/LICENSE). MIT. Mixed-source litmus files appear in the joint-source section.

```text
/*
* Copyright 2025 ByteDance Ltd. and/or its affiliates
*
* Permission is hereby granted, free of charge, to any person obtaining
* a copy of this software and associated documentation files
* (the "Software"), to deal in the Software without restriction,
* including without limitation the rights to use, copy, modify, merge,
* publish, distribute, sublicense, and/or sell copies of the Software,
* and to permit persons to whom the Software is furnished to do so,
* subject to the following conditions:
*
* The above copyright notice and this permission notice shall be
* included in all copies or substantial portions of the Software.
*
* THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
* EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
* MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
* IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
* CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
* TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
* SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
*/
```

### Sources under `MIT`

| File identifiers | Pinned source files |
| --- | --- |
| `VeriTile/Dist/Frontend/TritonExt/SourceHelpers.lean` | [allgather_group_gemm.py](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/kernels/nvidia/allgather_group_gemm.py) · [moe_reduce_ar.py](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/kernels/nvidia/moe_reduce_ar.py) · [moe_reduce_rs.py](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/kernels/nvidia/moe_reduce_rs.py) · [04-deepseek-infer-all2all.py](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/tutorials/04-deepseek-infer-all2all.py) · [common_ops.py](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/kernels/nvidia/common_ops.py) · [all_to_all_single_2d.py](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/kernels/nvidia/all_to_all_single_2d.py) |
| `VeriTile/Dist/Frontend/TritonExt/SignedSum.lean` | [all_to_all_single_2d.py](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/kernels/nvidia/all_to_all_single_2d.py) |
| `tests/lean/dist/SourceHelpers.lean` | [allgather_group_gemm.py](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/kernels/nvidia/allgather_group_gemm.py) · [moe_reduce_ar.py](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/kernels/nvidia/moe_reduce_ar.py) · [moe_reduce_rs.py](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/kernels/nvidia/moe_reduce_rs.py) · [04-deepseek-infer-all2all.py](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/tutorials/04-deepseek-infer-all2all.py) · [common_ops.py](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/kernels/nvidia/common_ops.py) · [ep_all2all_fused.py](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/kernels/nvidia/ep_all2all_fused.py) · [low_latency_all_to_all_v2.py](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/kernels/nvidia/low_latency_all_to_all_v2.py) |
| `VeriTile/Dist/Frontend/TritonExt/ProcedureHelpers.lean`, `tests/lean/dist/ProcedureHelpers.lean` | [all_to_all_vdev_2d_offset_inter_node.py](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/kernels/nvidia/all_to_all_vdev_2d_offset_inter_node.py) · [reduce_scatter.py](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/kernels/nvidia/reduce_scatter.py) |
| `tests/lean/dist/P2PTransferViews.lean` | [p2p.py](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/kernels/nvidia/p2p.py) |
| `tests/lean/dist/ElementHelper.lean` | [all_to_all_single_2d.py](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/kernels/nvidia/all_to_all_single_2d.py) |
| `a05` | [08-overlapping-gemm-reduce-scatter.py](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/tutorials/08-overlapping-gemm-reduce-scatter.py) |
| `a06` | [common_ops.py](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/kernels/nvidia/common_ops.py) |
| `b01`, `b04` | [triton-dist.semantics.rst](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/docs/python-api/triton-dist.semantics.rst) |
| `b02`, `b03`, `b13` | [01-distributed-notify-wait.py](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/tutorials/01-distributed-notify-wait.py) |
| `b07`, `b08` | [07-overlapping-allgather-gemm.py](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/tutorials/07-overlapping-allgather-gemm.py) |
| `b10`, `c01` | [03-inter-node-allgather.py](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/tutorials/03-inter-node-allgather.py) |
| `c05`, `scripts/census/fixtures/04-deepseek-infer-all2all.py.txt` | [04-deepseek-infer-all2all.py](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/tutorials/04-deepseek-infer-all2all.py) |

## TileScale

[Source and licence at `71e71457d40ed6e6a2dad297936bfdbff21d104b`](https://github.com/tile-ai/tilescale/blob/71e71457d40ed6e6a2dad297936bfdbff21d104b/LICENSE). MIT. The version 1 files use [the second pin](https://github.com/tile-ai/tilescale/blob/9ba8a605d347f600a95d0275e2639cb00122c084/LICENSE), which has the same licence text.

```text
    MIT License

    Copyright (c) Tile-AI.
    **During the period from December 1, 2024, to Mar 14, 2025, this project is
    subject to additional collaboration terms with Microsoft Corporation.**

    Permission is hereby granted, free of charge, to any person obtaining a copy
    of this software and associated documentation files (the "Software"), to deal
    in the Software without restriction, including without limitation the rights
    to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
    copies of the Software, and to permit persons to whom the Software is
    furnished to do so, subject to the following conditions:

    The above copyright notice and this permission notice shall be included in all
    copies or substantial portions of the Software.

    THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
    IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
    FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
    AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
    LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
    OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
    SOFTWARE
```

### Sources under `MIT`

| File identifiers | Pinned source files |
| --- | --- |
| `a07` | [deepep.md](https://github.com/tile-ai/tilescale/blob/9ba8a605d347f600a95d0275e2639cb00122c084/examples/distributed/deepseek_deepep/deepep.md) |
| `a08`, `b12` | [dispatch.py](https://github.com/tile-ai/tilescale/blob/9ba8a605d347f600a95d0275e2639cb00122c084/examples/distributed/deepseek_deepep/intranode/dispatch.py) |
| `a09` | [comm.py](https://github.com/tile-ai/tilescale/blob/71e71457d40ed6e6a2dad297936bfdbff21d104b/tilelang/language/distributed/comm.py) |
| `b09` | [example_allgather_gemm_overlapped.py](https://github.com/tile-ai/tilescale/blob/71e71457d40ed6e6a2dad297936bfdbff21d104b/examples/distributed/allgather_gemm/example_allgather_gemm_overlapped.py) |
| `b11` | [sync.py](https://github.com/tile-ai/tilescale/blob/71e71457d40ed6e6a2dad297936bfdbff21d104b/tilelang/language/distributed/sync.py) |

## TileLang

[Source and licence at `35850c06875bcc84751417982bf7b4d662bafdbc`](https://github.com/tile-ai/tilelang/blob/35850c06875bcc84751417982bf7b4d662bafdbc/LICENSE). MIT. Reference pin. No litmus implementation was derived from this repository.

```text
    MIT License

    Copyright (c) Tile-AI.
    **During the period from December 1, 2024, to Mar 14, 2025, this project is
    subject to additional collaboration terms with Microsoft Corporation.**

    Permission is hereby granted, free of charge, to any person obtaining a copy
    of this software and associated documentation files (the "Software"), to deal
    in the Software without restriction, including without limitation the rights
    to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
    copies of the Software, and to permit persons to whom the Software is
    furnished to do so, subject to the following conditions:

    The above copyright notice and this permission notice shall be included in all
    copies or substantial portions of the Software.

    THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
    IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
    FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
    AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
    LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
    OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
    SOFTWARE
```

## Triton

[Source and licence at `0add68262ab0a2e33b84524346cb27cbb2787356`](https://github.com/triton-lang/triton/blob/0add68262ab0a2e33b84524346cb27cbb2787356/LICENSE). MIT. The swizzle expansion and its arithmetic specification follow the pinned implementation. Conservatively credited vector-add examples are described in the inventory.

```text
/*
* Copyright 2018-2020 Philippe Tillet
* Copyright 2020-2022 OpenAI
*
* Permission is hereby granted, free of charge, to any person obtaining
* a copy of this software and associated documentation files
* (the "Software"), to deal in the Software without restriction,
* including without limitation the rights to use, copy, modify, merge,
* publish, distribute, sublicense, and/or sell copies of the Software,
* and to permit persons to whom the Software is furnished to do so,
* subject to the following conditions:
*
* The above copyright notice and this permission notice shall be
* included in all copies or substantial portions of the Software.
*
* THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
* EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
* MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
* IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
* CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
* TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
* SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
*/
```

### Sources under `MIT`

| File identifiers | Pinned source files |
| --- | --- |
| `README.md`, `bench/examples/VectorAdd/Kernels.lean`, `bench/examples/VectorAdd/VectorAdd.py`, `experiments/interp_gpu/smoke/kernels.py` | [01-vector-add.py](https://github.com/triton-lang/triton/blob/0add68262ab0a2e33b84524346cb27cbb2787356/python/tutorials/01-vector-add.py) |
| `VeriTile/Dist/Frontend/TritonExt/Swizzle.lean`, `tests/lean/dist/SwizzleSource.lean` | [standard.py](https://github.com/triton-lang/triton/blob/0add68262ab0a2e33b84524346cb27cbb2787356/python/triton/language/standard.py) |

## DeepEP

[Source and licence at `b57e5e212ab75350f53c72064333e4fe1076b1da`](https://github.com/deepseek-ai/DeepEP/blob/b57e5e212ab75350f53c72064333e4fe1076b1da/LICENSE). MIT. Reference pin. No litmus implementation was derived from this repository.

```text
MIT License

Copyright (c) 2025 DeepSeek

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
```

## NVIDIA CCCL (libcu++)

NVIDIA Corporation is identified as the documentation copyright holder. The `docs/` tree at this pin has no separate grant for that tree. For the libcu++ examples we infer `Apache-2.0 WITH LLVM-exception` from the libcu++ entry in the root `LICENSE` and the component text. [Root licence, lines 1–4](https://github.com/NVIDIA/cccl/blob/5d63af4077b8ae9c569d55428cb2cdc8ebbc31a5/LICENSE#L1-L4) · [libcu++ licence](https://github.com/NVIDIA/cccl/blob/5d63af4077b8ae9c569d55428cb2cdc8ebbc31a5/libcudacxx/LICENSE.TXT) · [Component licence overview](https://github.com/NVIDIA/cccl/blob/5d63af4077b8ae9c569d55428cb2cdc8ebbc31a5/docs/contributors/license.rst) · [Documentation copyright](https://github.com/NVIDIA/cccl/blob/5d63af4077b8ae9c569d55428cb2cdc8ebbc31a5/docs/conf.py#L25).

### Sources under `Apache-2.0 WITH LLVM-exception`

| File identifiers | Pinned source files |
| --- | --- |
| `a01`, `a02` | [memory_model.rst](https://github.com/NVIDIA/cccl/blob/5d63af4077b8ae9c569d55428cb2cdc8ebbc31a5/docs/libcudacxx/extended_api/memory_model.rst) |

## Locally authored litmus designs

These files implement the project’s original litmus specifications at [the S8.1 revision](https://github.com/VeriInfra-Lab/VeriTile-2/blob/51419efee8944c00d6d6a8296bf708ad2956b1d7/documents/dist/LitmusTable.md). Their MIT identifier applies to the project implementation. The NVIDIA NVSHMEM 3.6.5 manual supplies the API requirements cited in the table.

### Sources under `MIT`

| File identifiers | Pinned source files |
| --- | --- |
| `b05`, `b06`, `c02`, `c03`, `c04`, `c06`, `c07`, `c08` | [LitmusTable.md](https://github.com/VeriInfra-Lab/VeriTile-2/blob/51419efee8944c00d6d6a8296bf708ad2956b1d7/documents/dist/LitmusTable.md) |

## Jointly attributed litmus sources

These files combine the libcu++ examples and MIT material from the separately named repositories. Their expressions preserve the order in the existing mixed-source headers.

### Sources under `(Apache-2.0 WITH LLVM-exception) AND MIT`

| File identifiers | Pinned source files |
| --- | --- |
| `a03` | [memory_model.rst](https://github.com/NVIDIA/cccl/blob/5d63af4077b8ae9c569d55428cb2cdc8ebbc31a5/docs/libcudacxx/extended_api/memory_model.rst) · [common_ops.py](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/kernels/nvidia/common_ops.py) |
| `a10` | [atomic_thread_fence.rst](https://github.com/NVIDIA/cccl/blob/5d63af4077b8ae9c569d55428cb2cdc8ebbc31a5/docs/libcudacxx/extended_api/synchronization_primitives/atomic/atomic_thread_fence.rst) · [builtin.py](https://github.com/tile-ai/tilescale/blob/71e71457d40ed6e6a2dad297936bfdbff21d104b/tilelang/language/builtin.py) |

### Sources under `MIT AND (Apache-2.0 WITH LLVM-exception)`

| File identifiers | Pinned source files |
| --- | --- |
| `a04` | [triton-dist.semantics.rst](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/docs/python-api/triton-dist.semantics.rst) · [memory_model.rst](https://github.com/NVIDIA/cccl/blob/5d63af4077b8ae9c569d55428cb2cdc8ebbc31a5/docs/libcudacxx/extended_api/memory_model.rst) |

### Sources under `MIT`

| File identifiers | Pinned source files |
| --- | --- |
| `c09` | [copy_op.py](https://github.com/tile-ai/tilescale/blob/71e71457d40ed6e6a2dad297936bfdbff21d104b/tilelang/language/copy_op.py) · [builtin.py](https://github.com/tile-ai/tilescale/blob/71e71457d40ed6e6a2dad297936bfdbff21d104b/tilelang/language/builtin.py) |

## TritonBench-G and TorchAO

The redistributed FP4 snapshot comes from the [Apache-2.0 TritonBench corpus](https://github.com/thunlp/TritonBench/blob/603e28a5050e8c268f6883a69709d477a272d49a/LICENSE). Its [task metadata](https://github.com/thunlp/TritonBench/blob/603e28a5050e8c268f6883a69709d477a272d49a/data/TritonBench_G_v1.json) identifies `pytorch/ao`. The original TorchAO file says “Copyright (c) Meta Platforms, Inc. and affiliates.” Its [BSD-3-Clause licence](https://github.com/pytorch/ao/blob/52b6f4d9f9e8dbd5c2e96582f0b39354bfc823b6/LICENSE) says “Copyright 2023 Meta”. Both notices accompany the fixtures. The table records the matched historical source revision; the corpus does not pin its TorchAO revision.

### Sources under `Apache-2.0 AND BSD-3-Clause`

| File identifiers | Pinned source files |
| --- | --- |
| `experiments/floating_point/value_validation/fp4_unscaled/reference/original.py`, `experiments/floating_point/value_validation/fp4_unscaled/reference/original_jit.py` | [fp4_to_bf16.py](https://github.com/thunlp/TritonBench/blob/603e28a5050e8c268f6883a69709d477a272d49a/data/TritonBench_G_v1/fp4_to_bf16.py) · [custom_cast.py](https://github.com/pytorch/ao/blob/52b6f4d9f9e8dbd5c2e96582f0b39354bfc823b6/torchao/prototype/mx_formats/custom_cast.py) |

## Historical kernel fixtures and derived code

The three intact Python test fixtures match TritonBench Git blobs at its pinned revision. The [corpus metadata](https://github.com/thunlp/TritonBench/blob/603e28a5050e8c268f6883a69709d477a272d49a/data/TritonBench_G_v1.json) attributes them to Triton, ThunderKittens and FlagGems. The original repositories below establish the underlying sources. The historical revisions are comparable sources. The corpus did not identify the exact revisions it imported.

- Seeded dropout matches Triton's tutorial, under the Triton MIT notice above. The frontend's Philox model uses the [Triton v3.7.1 MIT licence](https://github.com/triton-lang/triton/blob/f797708c0626e5f9840ca5b0a98790e2c7cb09ad/LICENSE).
- Layer normalization includes the one-pass kernel and wrapper from ThunderKittens, which retain “Copyright (c) 2024, Tri Dao.” and credit Triton's layer-normalization tutorial. The corresponding FlashAttention implementation carries the same notice. Retain the [HazyResearch MIT notice](https://github.com/HazyResearch/ThunderKittens/blob/cdfce886b2660a0345a20bc5c7d52efd0db95fc0/LICENSE) (Copyright (c) 2024 HazyResearch, with the MIT permission text above) and [FlashAttention BSD-3-Clause notice](licenses/BSD-3-Clause-FlashAttention.txt) (Copyright (c) 2022, the respective contributors, as shown by the [AUTHORS file](https://github.com/Dao-AILab/flash-attention/blob/0dfb28174333d9eefb7c1dd4292690a8458d1e89/AUTHORS)).
- Uniform sampling combines FlagGems' generator and random helpers, including a fallback explicitly copied from Triton. FlagGems' [Apache-2.0 licence](https://github.com/FlagOpen/FlagGems/blob/72331cfb52c0f9e4fc12146803843b5a13b41c81/LICENSE) says “Copyright © 2024 BAAI. All rights reserved.” The Lean kernel calls the helper, whereas the Python fixture and frontend canonical string reproduce its implementation.
- The Random123 test data carries its [distribution notice](https://github.com/DEShawResearch/random123/blob/726a093cd9a73f3ec3c8d7a70ff10ed8efec8d13/LICENSE), Copyright 2010-2012, D. E. Shaw Research.

- The attention quotation copies the [MIT-licensed historical Lean port](https://github.com/VeriInfra-Lab/VeriTile-2/blob/f71dffb1dc5bcf20f6680f318a83d852dd1e921f/LICENSE), Copyright (c) 2026 Zenan Li. The Python corpus file preserves the two JIT functions from the pinned historical SageAttention source. That revision uses its [BSD-3-Clause licence](licenses/BSD-3-Clause-SageAttention.txt), Copyright (c) 2024, Jintao Zhang. The local closed-form proof applies to this quoted surface kernel.

### Sources under `Apache-2.0 AND BSD-3-Clause AND MIT`

| File identifiers | Pinned source files |
| --- | --- |
| `VeriTile/Examples/AttentionForwardClosedForm.lean` | [data/TritonBench_G_v1/attention_forward_triton.py](https://github.com/thunlp/TritonBench/blob/603e28a5050e8c268f6883a69709d477a272d49a/data/TritonBench_G_v1/attention_forward_triton.py) · [sageattention/attn_qk_int8_per_block_h96.py](https://github.com/thu-ml/SageAttention/blob/1d8f5314f0a6ec6d5f9a63bf0e60a0b55da80dac/sageattention/attn_qk_int8_per_block_h96.py) · [bench/tritonbench_g/attention_forward_triton/AttentionForwardTriton.lean](https://github.com/VeriInfra-Lab/VeriTile-2/blob/f71dffb1dc5bcf20f6680f318a83d852dd1e921f/bench/tritonbench_g/attention_forward_triton/AttentionForwardTriton.lean) |

### Sources under `Apache-2.0 AND MIT`

| File identifiers | Pinned source files |
| --- | --- |
| `scripts/fixtures/source_materializations/seeded_dropout.py.txt` | [data/TritonBench_G_v1/seeded_dropout.py](https://github.com/thunlp/TritonBench/blob/603e28a5050e8c268f6883a69709d477a272d49a/data/TritonBench_G_v1/seeded_dropout.py) · [python/tutorials/04-low-memory-dropout.py](https://github.com/triton-lang/triton/blob/0add68262ab0a2e33b84524346cb27cbb2787356/python/tutorials/04-low-memory-dropout.py) |
| `scripts/fixtures/source_materializations/Kernels.lean.txt` | [data/TritonBench_G_v1/seeded_dropout.py](https://github.com/thunlp/TritonBench/blob/603e28a5050e8c268f6883a69709d477a272d49a/data/TritonBench_G_v1/seeded_dropout.py) · [python/tutorials/04-low-memory-dropout.py](https://github.com/triton-lang/triton/blob/0add68262ab0a2e33b84524346cb27cbb2787356/python/tutorials/04-low-memory-dropout.py) |
| `scripts/fixtures/source_uniform_materializations/uniform_sampling.py.txt` | [data/TritonBench_G_v1/uniform_sampling.py](https://github.com/thunlp/TritonBench/blob/603e28a5050e8c268f6883a69709d477a272d49a/data/TritonBench_G_v1/uniform_sampling.py) · [src/flag_gems/ops/uniform.py](https://github.com/FlagOpen/FlagGems/blob/72331cfb52c0f9e4fc12146803843b5a13b41c81/src/flag_gems/ops/uniform.py) · [src/flag_gems/utils/random_utils.py](https://github.com/FlagOpen/FlagGems/blob/72331cfb52c0f9e4fc12146803843b5a13b41c81/src/flag_gems/utils/random_utils.py) · [python/triton/language/random.py](https://github.com/triton-lang/triton/blob/0add68262ab0a2e33b84524346cb27cbb2787356/python/triton/language/random.py) |
| `VeriTile/Triton/DSL/UniformJitFunctions.lean` | [data/TritonBench_G_v1/uniform_sampling.py](https://github.com/thunlp/TritonBench/blob/603e28a5050e8c268f6883a69709d477a272d49a/data/TritonBench_G_v1/uniform_sampling.py) · [src/flag_gems/utils/random_utils.py](https://github.com/FlagOpen/FlagGems/blob/72331cfb52c0f9e4fc12146803843b5a13b41c81/src/flag_gems/utils/random_utils.py) · [python/triton/language/random.py](https://github.com/triton-lang/triton/blob/0add68262ab0a2e33b84524346cb27cbb2787356/python/triton/language/random.py) |

### Sources under `Apache-2.0 AND MIT AND BSD-3-Clause`

| File identifiers | Pinned source files |
| --- | --- |
| `scripts/fixtures/source_control_materializations/layer_norm_fwd.py.txt` | [data/TritonBench_G_v1/layer_norm_fwd.py](https://github.com/thunlp/TritonBench/blob/603e28a5050e8c268f6883a69709d477a272d49a/data/TritonBench_G_v1/layer_norm_fwd.py) · [tests/python/layernorm/baselines/layer_norm_triton.py](https://github.com/HazyResearch/ThunderKittens/blob/cdfce886b2660a0345a20bc5c7d52efd0db95fc0/tests/python/layernorm/baselines/layer_norm_triton.py) · [flash_attn/ops/triton/layer_norm.py](https://github.com/Dao-AILab/flash-attention/blob/0dfb28174333d9eefb7c1dd4292690a8458d1e89/flash_attn/ops/triton/layer_norm.py) · [python/tutorials/05-layer-norm.py](https://github.com/triton-lang/triton/blob/0add68262ab0a2e33b84524346cb27cbb2787356/python/tutorials/05-layer-norm.py) |
| `scripts/fixtures/source_control_materializations/Kernels.lean.txt` | [data/TritonBench_G_v1/layer_norm_fwd.py](https://github.com/thunlp/TritonBench/blob/603e28a5050e8c268f6883a69709d477a272d49a/data/TritonBench_G_v1/layer_norm_fwd.py) · [tests/python/layernorm/baselines/layer_norm_triton.py](https://github.com/HazyResearch/ThunderKittens/blob/cdfce886b2660a0345a20bc5c7d52efd0db95fc0/tests/python/layernorm/baselines/layer_norm_triton.py) · [flash_attn/ops/triton/layer_norm.py](https://github.com/Dao-AILab/flash-attention/blob/0dfb28174333d9eefb7c1dd4292690a8458d1e89/flash_attn/ops/triton/layer_norm.py) · [python/tutorials/05-layer-norm.py](https://github.com/triton-lang/triton/blob/0add68262ab0a2e33b84524346cb27cbb2787356/python/tutorials/05-layer-norm.py) |

### Sources under `Apache-2.0`

| File identifiers | Pinned source files |
| --- | --- |
| `scripts/fixtures/source_uniform_materializations/Kernels.lean.txt` | [data/TritonBench_G_v1/uniform_sampling.py](https://github.com/thunlp/TritonBench/blob/603e28a5050e8c268f6883a69709d477a272d49a/data/TritonBench_G_v1/uniform_sampling.py) · [src/flag_gems/ops/uniform.py](https://github.com/FlagOpen/FlagGems/blob/72331cfb52c0f9e4fc12146803843b5a13b41c81/src/flag_gems/ops/uniform.py) |

### Sources under `MIT`

| File identifiers | Pinned source files |
| --- | --- |
| `VeriTile/Triton/Random/Philox.lean` | [python/triton/language/random.py](https://github.com/triton-lang/triton/blob/f797708c0626e5f9840ca5b0a98790e2c7cb09ad/python/triton/language/random.py) |
| `site/src/lib/vector-add-record.json` | [python/tutorials/01-vector-add.py](https://github.com/triton-lang/triton/blob/0add68262ab0a2e33b84524346cb27cbb2787356/python/tutorials/01-vector-add.py) |

### Sources under `BSD-3-Clause`

| File identifiers | Pinned source files |
| --- | --- |
| `tests/lean/PhiloxRandom.lean` | [tests/kat_vectors](https://github.com/DEShawResearch/random123/blob/726a093cd9a73f3ec3c8d7a70ff10ed8efec8d13/tests/kat_vectors) |

## Inventory outside the litmus suite

Audited the tracked source tree at `813b9fb5c` on 2026-11-24, including the bench provenance map, kernel quotations, frontend adapters, test formulas, experiment reference snapshots, and the repository history of the vector-add example. Comparing every tracked blob at that revision to all 184 upstream Python blob IDs found four exact copies: FP4, seeded dropout, layer normalization and uniform sampling. Line ranges for these and the translated excerpts are in the headers or adjacent records. The remaining random-profile and proof snapshots in the three fixture directories preserve local adapters, index-domain definitions and proofs. The [TileLang selection](bench/tilelang/examples/SELECTION.md) records proposed source choices; its directory contains a plan and no kernel implementation at this revision.

| Repository candidate | Classification and evidence |
| --- | --- |
| `VeriTile/Dist/Frontend/TritonExt/Swizzle.lean` | Derived. The expansion follows Triton's linear index, group, shortened last group, remainder and final coordinates in order. It adds local validation and fresh registers. [Triton v3.5.1, lines 77–114](https://github.com/triton-lang/triton/blob/0add68262ab0a2e33b84524346cb27cbb2787356/python/triton/language/standard.py#L77-L114) |
| `tests/lean/dist/SwizzleSource.lean` | Derived formula in `result_formula`; the public kernel execution and proof are local. |
| `VeriTile/Dist/Frontend/TritonExt/Constexpr.lean` | Local implementation of documented operations. It checks static shape, bindings and bounds; integer specialization calls Lean's `Nat.nextPowerOfTwo`. The pinned inputs supply call spellings and the specification. [Distributed helper](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/kernels/nvidia/common_ops.py#L270-L272) |
| `bench/examples/VectorAdd/VectorAdd.py` | Conservatively attributed adaptation. The [retained project source](https://github.com/VeriInfra-Lab/VeriTile/blob/3dda9e5a5dfbc7f77f82509f044eb5a8afe7345e/bench/examples/VectorAdd/vector_add.py) matches the load, addition and store sequence of the [Triton tutorial](https://github.com/triton-lang/triton/blob/0add68262ab0a2e33b84524346cb27cbb2787356/python/tutorials/01-vector-add.py#L29-L53) with the mask removed. The historical record does not identify the exact external revision used by the author. |
| `bench/examples/VectorAdd/Kernels.lean` | Derived through that Python body. The two quotations preserve the full tile and its commuted addition. |
| `README.md` | Derived excerpt. The quick start reproduces the six-line body of this vector-add quotation and links its Python source. |
| `experiments/interp_gpu/smoke/kernels.py` | Conservatively attributed masked tutorial-style add; the GPU launch, sentinel check and Torch harness functions are local. |
| `experiments/floating_point/value_validation/fp4_unscaled/reference/original.py` | Derived. Byte-identical to the fixed TritonBench-G source (SHA-256 `8571cb56ce932af6a7dd68e4047ee0863984812ac303d0d2959fc544a65e9958`). The corpus identifies TorchAO, whose historical kernel has an identical Python AST and whose helper uses the same bit unpack, special cases and conversion. |
| `experiments/floating_point/value_validation/fp4_unscaled/reference/original_jit.py` | Derived. The [experiment's extraction and digest record](experiments/floating_point/value_validation/fp4_unscaled/reference/reference.json) binds its exact two decorated functions from the preceding file. These two frozen payloads keep byte-identical source and nearby three-line attribution sidecars; prepending comments would invalidate their accepted source, line and extraction receipts. A proposal to embed the headers must version and regenerate the reference and revalidate the experiment before replacing those bytes. |
| `scripts/fixtures/source_materializations/seeded_dropout.py.txt` | Derived. The complete Python fixture has the same Git blob ID as its pinned corpus file. |
| `scripts/fixtures/source_materializations/Kernels.lean.txt` | Derived. This frozen Lean fixture transcribes the two-variant seeded dropout kernel. Its fixture README records the SHA-256. |
| `scripts/fixtures/source_control_materializations/layer_norm_fwd.py.txt` | Derived. The complete Python fixture has the same Git blob ID as its pinned corpus file. |
| `scripts/fixtures/source_control_materializations/Kernels.lean.txt` | Derived. This frozen Lean fixture transcribes the one-pass layer-normalization kernel with residual and dropout branches. Its fixture README records the SHA-256. |
| `scripts/fixtures/source_uniform_materializations/uniform_sampling.py.txt` | Derived. The complete Python fixture has the same Git blob ID as its pinned corpus file. |
| `scripts/fixtures/source_uniform_materializations/Kernels.lean.txt` | Derived. This frozen Lean fixture transcribes the four-result uniform generator kernel. Its fixture README records the SHA-256. |
| `VeriTile/Triton/DSL/UniformJitFunctions.lean` | Derived. Its canonical string embeds the copied FlagGems/Triton dtype-dispatch fallback body. |
| `VeriTile/Triton/Random/Philox.lean` | Conservatively attributed. The 32-bit round and key-update expressions and uniform conversion reproduce the named Triton 3.7.1 algorithm. |
| `tests/lean/PhiloxRandom.lean` | Derived data. The six independent test vectors are transcribed from Random123. Local rounding and decoder checks follow. |
| `site/src/lib/vector-add-record.json` | Derived quotation. The generated homepage proof record embeds the six-line add body and its mutation. It uses a sidecar because its JSON format has no comments. |
| `VeriTile/Examples/AttentionForwardClosedForm.lean` | Derived surface quotation. All 61 lines of the surface kernel match the historical Lean port. Its two fixed Python JIT functions match the historical SageAttention functions by AST. The closed-form proofs are local. |
| Remaining 17 local bench Python examples and their Lean quotations | Locally authored from independent specifications; the [per-example provenance table](bench/examples/SOURCE_PROVENANCE.md) identifies each file. The separately hosted `TritonBenchVectorAddition` example belongs to the external corpus review below. |
| `bench/tritonbench_g/*/*.py` | Moved out of this repository. The inventory above covers the retained corpus payloads, quotations and frozen translations in other directories. A fix in the owning repository is still required. |

### TritonBench-G redistribution handoff

[Issue #4](https://github.com/VeriInfra-Lab/VeriTile-2/issues/4) recorded 173 copied Python sources with added annotations. At the pinned revisions there are **184** one-task Python files in [VeriTileBench's corpus](https://github.com/VeriInfra-Lab/VeriTileBench/tree/38f575bf4a08c91ab36df2393e42a895adc50d06/bench/tritonbench_g) and 184 in [TritonBench's corpus](https://github.com/thunlp/TritonBench/tree/603e28a5050e8c268f6883a69709d477a272d49a/data/TritonBench_G_v1). Pair `bench/tritonbench_g/<task>/<task>.py` with `data/TritonBench_G_v1/<task>.py`. All 184 basenames match; all paired Git blob IDs differ. A differing blob identifies a file for inspection, not the nature of the edit.

The follow-up belongs in **VeriInfra-Lab/VeriTileBench**. Its deliverable is a 184-row manifest plus the [separate example](https://github.com/VeriInfra-Lab/VeriTileBench/blob/38f575bf4a08c91ab36df2393e42a895adc50d06/bench/examples/TritonBenchVectorAddition/TritonBenchVectorAddition.py) and corresponding Lean translations. For each task, use the [dataset's `file` and `repo` fields](https://github.com/thunlp/TritonBench/blob/603e28a5050e8c268f6883a69709d477a272d49a/data/TritonBench_G_v1.json) to trace file-level notices, holders and licence texts in the original repository as well as the Apache-2.0 corpus. Review the diff, identify modifications explicitly, retain applicable notices and place the licence texts with the distribution. Flag unresolved or restricted origins for review before redistribution. Acceptance is a one-to-one source/translation inventory, checked headers and real pins/paths, the four attribution mutations, and the owning repository's source-correspondence and receipt checks for changed bytes. Neither pinned corpus tree contains a root `NOTICE` file.
