# Interpreter example specs

Build the file runner from the repository root, then execute the specs with uv. The script declares its Draft 7 validator, `jsonschema==4.25.1`.

```sh
lake build veritile-run
uv run --no-project --python 3.11 --script experiments/interp_gpu/specs/examples/run.py
```

Pass specific JSON paths to select examples. The driver validates each [spec](../schema.json), checks the qualified Lean declaration and the top-level `@triton.jit` function in the checked-out example source, reads the declared version-1 input tensors and calls the public executable with its grid, carrier and ordered files. It reads each returned tensor, checks its declared dtype and shape, and compares the complete bytes with the case's independent fixture. It creates and removes a temporary directory per case. The optional Triton launch fields document the corresponding GPU launch configuration. This command runs locally on the CPU.

[VectorAdd](VectorAdd.json) runs two programs over aligned FP32 vectors of length four. [OnlineSoftmax](OnlineSoftmax.json) runs one program per row on equal, increasing and decreasing pairs. Two rows produce underflow at one lane. The expected buffers are the checked-in file-runner fixtures.

## Benchmark task families

The [assignment table](../ASSIGNMENT.tsv) gives each of the 183 tritonbench tasks one family and marks the ten I9.3 smoke entry points.

| Code | Task family |
| --- | --- |
| [A1](https://github.com/VeriInfra-Lab/VeriTile-2/issues/131) | Elementwise operations, activations and sampling |
| [A2](https://github.com/VeriInfra-Lab/VeriTile-2/issues/132) | Normalization, softmax, reductions and losses |
| [B1](https://github.com/VeriInfra-Lab/VeriTile-2/issues/133) | Matrix multiplication and quantization |
| [B2](https://github.com/VeriInfra-Lab/VeriTile-2/issues/134) | Copy, indexing, cumulative sums and caches |
| [C1](https://github.com/VeriInfra-Lab/VeriTile-2/issues/135) | Attention |
| [C2](https://github.com/VeriInfra-Lab/VeriTile-2/issues/136) | Recurrent and chunked sequences, rotary operations and concurrent tasks |

## Source and binding coverage

There are 18 local worked-example directories. The [source inventory](../../../../documents/InterpReflectCoverage.md) identifies all 68 Lean definitions, 62 of which have checked mirrors. The registry binds 16 mirrors across 12 families. Four use the [FP32 runner](../../../../tests/interp/Main.lean). The other 12 use the [binary64 file bindings](../../../../tests/interp/TensorExamples.lean), including [HyperConnections](../../../../tests/interp/HyperConnections.lean). Each binding validates its own input dtypes, shapes and launch parameters. The additional historic TritonBenchVectorAddition group listed in the [worked-example catalogue](../../../../bench/examples/README.md) is hosted in VeriTileBench.

| Local family and source | Reflected / defined | File-runner binding or required work |
| --- | ---: | --- |
| [AdamUpdateGridLaunch](../../../../bench/examples/AdamUpdateGridLaunch/AdamUpdateGridLaunch.py) | 4/4 | [AdamUpdateGridLaunch](AdamUpdateGridLaunch.json) reads three FP32 vectors and writes both updated input regions. The fixture includes a masked tail and zero, positive and negative updates. The mirror specializes `chunk_elements = n_elements`. |
| [FlatVectorAdd](../../../../bench/examples/FlatVectorAdd/FlatVectorAdd.py) | 4/4 | [Runnable spec](FlatVectorAdd.json). Independent `blockSize=4` and `nElements=5` bindings exercise one active lane in the last block. |
| [FloatDTypeAdd](../../../../bench/examples/FloatDTypeAdd/FloatDTypeAdd.py) | 4/4 | [Runnable spec](FloatDTypeAdd.json). The FP32 loads, sum, explicit output cast and store run over signed pairs including halfway rounding and negative zero. |
| [FloatDTypeSoftmax](../../../../bench/examples/FloatDTypeSoftmax/FloatDTypeSoftmax.py) | 4/5 | Unregistered. Arithmetic uses FP64 with FP32 inputs/outputs. The body projection in `commonPrefix` has no mirror. |
| [FusedLayerNorm](../../../../bench/examples/FusedLayerNorm/FusedLayerNorm.py) | 2/2 | [FusedLayerNorm](FusedLayerNorm.json) binds a physical FP32 matrix, two channel vectors, epsilon and row stride. The fixture uses five physical cells for four channels and exports a dense BF16 matrix. |
| [FusedSiLU](../../../../bench/examples/FusedSiLU/FusedSiLU.py) | 4/5 | [FusedSiLU](FusedSiLU.json) reads three FP64 vectors and writes BF16. [Gate](FusedSiLUGate.json), [activation](FusedSiLUActivation.json) and [residual](FusedSiLUResidual.json) bind the three real unfused stages. The executable regression passes the two FP64 intermediate files from each stage to the next. |
| [FusedSwiglu](../../../../bench/examples/FusedSwiglu/FusedSwiglu.py) | 3/4 | Unregistered. Bind mask extent and BF16 intermediate/output casts. The body projection in `swiglu_unfused` has no mirror. |
| [HyperConnectionsDepth](../../../../bench/examples/HyperConnectionsDepth/HyperConnectionsDepth.py) | 6/7 | [Matrix](HyperConnectionsDepth.json) binds residual mix `[B,S,D]`, branch output `[B,T,D]` and logits `[T,S]`, plus temperature and normalization iterations. [Scalar](HyperConnectionsDepthScalar.json) binds two vectors and one shared logit. |
| [HyperConnectionsWidth](../../../../bench/examples/HyperConnectionsWidth/HyperConnectionsWidth.py) | 8/9 | [HyperConnectionsWidth](HyperConnectionsWidth.json) binds residuals `[B,S,D]`, residual logits `[S,S]` and branch logits `[S,T]`. It publishes both the FP32 residual mix `[B,S,D]` and branch input `[B,T,D]`. |
| [LogExp](../../../../bench/examples/LogExp/LogExp.py) | 2/2 | Unregistered. The source requires libdevice log and exp, with abs and fallback in the guarded variant. |
| [OnlineSoftmax](../../../../bench/examples/OnlineSoftmax/OnlineSoftmax.py) | 3/3 | `OnlineSoftmax` runs `onlineSoftmaxKernel` with fixed ports x/y and N bound to row width. The stable and batch definitions lack entries. |
| [RowWiseMax](../../../../bench/examples/RowWiseMax/RowWiseMax.py) | 2/2 | [RowWiseMax](RowWiseMax.json) returns one FP32 maximum per matrix row, including an all-negative row. |
| [RowWiseSum](../../../../bench/examples/RowWiseSum/RowWiseSum.py) | 2/2 | [RowWiseSum](RowWiseSum.json) returns one FP32 sum per matrix row. |
| [SoftmaxReciprocal](../../../../bench/examples/SoftmaxReciprocal/SoftmaxReciprocal.py) | 4/5 | Unregistered. Bind reductions and BF16 result encoding. The body projection in `commonPrefix` has no mirror. |
| [SoftmaxStable](../../../../bench/examples/SoftmaxStable/SoftmaxStable.py) | 2/2 | Unregistered. Bind FP32 sums, the stable variant's maximum, and BF16 results. |
| [StableLogSumExp](../../../../bench/examples/StableLogSumExp/StableLogSumExp.py) | 2/2 | Unregistered. Return a BF16 scalar per input row, with log-exp and reduction support. |
| [VectorAdd](../../../../bench/examples/VectorAdd/VectorAdd.py) | 4/4 | `VectorAdd` runs `originalKernel` with fixed ports x/y/out and block width bound to vector length divided by grid X. The other three definitions lack individual entries. |
| [Welford](../../../../bench/examples/Welford/Welford.py) | 2/2 | [Welford](Welford.json) reads a strided FP32 row and outputs independent length-one BF16 mean and population-variance files. Both source stores use address zero, so this entry accepts a one-program grid. |

Running an unregistered family by name exits with an unknown-kernel diagnostic. The six remaining families need the source-operation registrations tracked in [#647](https://github.com/VeriInfra-Lab/VeriTile-2/issues/647).

Reproduce the two vector fixtures with `python3 tests/interp/fixtures/vector_add_cases.py --check`. The generator uses Python arithmetic and IEEE binary32 packing independently of Lean. For these bindings, the driver forwards source constexpr names and values to `veritile-run` as repeated `--constexpr NAME=N` options before the kernel name.


## Heterogeneous file arguments

The `binary64` registrations run the reflected source with the [host interpreter](../../../../VeriTile/Interp/Carrier/Float.lean). It evaluates floating arithmetic in binary64. Runtime FP32 scalars are rounded to their source format before specialization. The file codec decodes FP32 and FP64 inputs, exports FP32/FP64 words and rounds BF16 directly from binary64 using ties to even. This carrier is a CPU reference approximation. The fixtures compare encoded values for these launches and do not establish hardware equivalence.

Pass source constants as `--constexpr NAME=NUMBER` and runtime scalars as `--scalar NAME=NUMBER` before the registry name. Positional arguments then give input tensor paths in source order and a single destination path. A single-output call writes a tensor file. A multi-output call publishes a new directory containing one `<port>.tensor` per output. The runner prepares every file before it renames that directory. For an in-place input such as Adam's `p_ptr`, provide its initial file as an input and read its updated value in the result directory.

Regenerate or verify the checked-in specs and fixtures with `python3 tests/interp/fixtures/tensor_examples.py` or `--check`. The generator uses scalar Python formulas, direct matrix balancing, independent byte packing and no runner output. Run `python3 tests/interp/check_example_mismatches.py` to flip one expected data bit at each new output and verify a mismatch through the public spec driver.
