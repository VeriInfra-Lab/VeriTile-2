# Interpreter example specs

Build the file runner from the repository root, then execute the specs with Python 3 and `jsonschema` (draft 7).

```sh
lake build veritile-run
python3 experiments/interp_gpu/specs/examples/run.py
```

Pass specific JSON paths to select examples. The driver validates each [spec](../schema.json), reads the declared version-1 input tensors and calls the public executable with its grid, carrier and ordered files. It reads each returned tensor, checks its declared dtype and shape, and compares the complete bytes with the case's independent fixture. It creates and removes a temporary directory per case. The optional Triton launch fields document the corresponding GPU launch configuration. This command runs locally on the CPU.

[VectorAdd](VectorAdd.json) runs two programs over aligned FP32 vectors of length four. [OnlineSoftmax](OnlineSoftmax.json) runs one program per row on equal, increasing and decreasing pairs. Two rows produce underflow at one lane. The expected buffers are the checked-in file-runner fixtures.

## Source and binding coverage

There are 18 local worked-example directories. The [source inventory](../../../../documents/InterpReflectCoverage.md) identifies all 68 Lean definitions, 62 of which have checked mirrors. The registry binds four of those mirrors. The [file interface](../../../../VeriTile/Interp/Run/Main.lean) accepts inputs of a common shape and returns one tensor of that shape. Its [FP32 carrier and bindings](../../../../tests/interp/Main.lean) implement only the arithmetic needed by the registered programs. The additional historic TritonBenchVectorAddition group listed in the [worked-example catalogue](../../../../bench/examples/README.md) is hosted in VeriTileBench.

| Local family and source | Reflected / defined | File-runner binding or required work |
| --- | ---: | --- |
| [AdamUpdateGridLaunch](../../../../bench/examples/AdamUpdateGridLaunch/AdamUpdateGridLaunch.py) | 4/4 | Unregistered. Bind the scalar update parameters and preserve both in-place outputs, parameters and exponential averages. |
| [FlatVectorAdd](../../../../bench/examples/FlatVectorAdd/FlatVectorAdd.py) | 4/4 | [Runnable spec](FlatVectorAdd.json). Independent `blockSize=4` and `nElements=5` bindings exercise one active lane in the last block. |
| [FloatDTypeAdd](../../../../bench/examples/FloatDTypeAdd/FloatDTypeAdd.py) | 4/4 | [Runnable spec](FloatDTypeAdd.json). The FP32 loads, sum, explicit output cast and store run over signed pairs including halfway rounding and negative zero. |
| [FloatDTypeSoftmax](../../../../bench/examples/FloatDTypeSoftmax/FloatDTypeSoftmax.py) | 4/5 | Unregistered. Arithmetic uses FP64 with FP32 inputs/outputs. The body projection in `commonPrefix` has no mirror. |
| [FusedLayerNorm](../../../../bench/examples/FusedLayerNorm/FusedLayerNorm.py) | 2/2 | Unregistered. Bind the row matrix and two channel vectors separately, along with epsilon and stride. The output is BF16. |
| [FusedSiLU](../../../../bench/examples/FusedSiLU/FusedSiLU.py) | 4/5 | Unregistered. Bind the fused inputs, BF16 output and the unfused pipeline's intermediates. The body projection in `unfusedSiLUKernel` has no mirror. |
| [FusedSwiglu](../../../../bench/examples/FusedSwiglu/FusedSwiglu.py) | 3/4 | Unregistered. Bind mask extent and BF16 intermediate/output casts. The body projection in `swiglu_unfused` has no mirror. |
| [HyperConnectionsDepth](../../../../bench/examples/HyperConnectionsDepth/HyperConnectionsDepth.py) | 6/7 | Unregistered. Bind scalar or matrix dimensions, three input regions and temperature. Matrix inputs have distinct layouts. Symbolic dispatch in `mhcDepthConnectionKernel` has no mirror. |
| [HyperConnectionsWidth](../../../../bench/examples/HyperConnectionsWidth/HyperConnectionsWidth.py) | 8/9 | Unregistered. Bind shapes separately and return both residual-mix and branch-input buffers. Symbolic dispatch in `mhcWidthConnectionKernel` has no mirror. |
| [LogExp](../../../../bench/examples/LogExp/LogExp.py) | 2/2 | Unregistered. The source requires libdevice log and exp, with abs and fallback in the guarded variant. |
| [OnlineSoftmax](../../../../bench/examples/OnlineSoftmax/OnlineSoftmax.py) | 3/3 | `OnlineSoftmax` runs `onlineSoftmaxKernel` with fixed ports x/y and N bound to row width. The stable and batch definitions lack entries. |
| [RowWiseMax](../../../../bench/examples/RowWiseMax/RowWiseMax.py) | 2/2 | Unregistered. Read a matrix, reduce each row by max and return one element per row. |
| [RowWiseSum](../../../../bench/examples/RowWiseSum/RowWiseSum.py) | 2/2 | Unregistered. Read a matrix, reduce each row by sum and return one element per row. |
| [SoftmaxReciprocal](../../../../bench/examples/SoftmaxReciprocal/SoftmaxReciprocal.py) | 4/5 | Unregistered. Bind reductions and BF16 result encoding. The body projection in `commonPrefix` has no mirror. |
| [SoftmaxStable](../../../../bench/examples/SoftmaxStable/SoftmaxStable.py) | 2/2 | Unregistered. Bind FP32 sums, the stable variant's maximum, and BF16 results. |
| [StableLogSumExp](../../../../bench/examples/StableLogSumExp/StableLogSumExp.py) | 2/2 | Unregistered. Return a BF16 scalar per input row, with log-exp and reduction support. |
| [VectorAdd](../../../../bench/examples/VectorAdd/VectorAdd.py) | 4/4 | `VectorAdd` runs `originalKernel` with fixed ports x/y/out and block width bound to vector length divided by grid X. The other three definitions lack individual entries. |
| [Welford](../../../../bench/examples/Welford/Welford.py) | 2/2 | Unregistered. Return two BF16 statistics, mean and variance, from the input row. |

Running an unregistered family by name exits with an unknown-kernel diagnostic. Additional file-runner registrations, support for the necessary operations and a generalized buffer interface are prerequisites for executing the other families through this client.

Reproduce the two vector fixtures with `python3 tests/interp/fixtures/vector_add_cases.py --check`. The generator uses Python arithmetic and IEEE binary32 packing independently of Lean. For these bindings, the driver forwards source constexpr names and values to `veritile-run` as repeated `--constexpr NAME=N` options before the kernel name.
