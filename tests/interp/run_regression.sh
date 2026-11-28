#!/usr/bin/env bash
# Run the compiled entry point against independently encoded version-1 tensor files.
set -euo pipefail
cd "$(dirname "$0")/../.."
lake build veritile-run
runner=.lake/build/bin/veritile-run
fixtures=tests/interp/fixtures
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

"$runner" --help
"$runner" --carrier fp32-basic --grid 2 VectorAdd "$fixtures/vector-x.tensor" \
  "$fixtures/vector-y.tensor" "$work/vector.tensor"
cmp "$work/vector.tensor" "$fixtures/vector-sum.tensor"

# Three programs exercise the two loop iterations with equal, decreasing and increasing logits.
"$runner" --carrier fp32-basic --grid 3,1,1 OnlineSoftmax "$fixtures/softmax-input.tensor" "$work/rows.tensor"
cmp "$work/rows.tensor" "$fixtures/softmax-output.tensor"

reject() {
  if "$runner" "$@"; then
    echo "Unexpected success: $*" >&2
    exit 1
  fi
}
# Source constants must match both the file shape and the actual launch.
reject --carrier fp32-basic --grid 2 --constexpr blockSize=4 --constexpr nElements=6 \
  FlatVectorAdd "$fixtures/flat-add-x.tensor" "$fixtures/flat-add-y.tensor" "$work/result.tensor"
reject --carrier fp32-basic --grid 1 --constexpr blockSize=4 --constexpr nElements=5 \
  FlatVectorAdd "$fixtures/flat-add-x.tensor" "$fixtures/flat-add-y.tensor" "$work/result.tensor"
reject --carrier fp32-basic --grid 3 --constexpr BLOCK_SIZE=3 \
  FloatDTypeAdd "$fixtures/float-add-x.tensor" "$fixtures/float-add-y.tensor" "$work/result.tensor"
reject --carrier fp32-basic --grid 3 --constexpr BLOCK_SIZE=2 --constexpr BLOCK_SIZE=2 \
  FloatDTypeAdd "$fixtures/float-add-x.tensor" "$fixtures/float-add-y.tensor" "$work/result.tensor"
reject --carrier fp32-basic --grid 2 --constexpr BLOCK_SIZE=2 \
  VectorAdd "$fixtures/vector-x.tensor" "$fixtures/vector-y.tensor" "$work/result.tensor"
reject --carrier missing --grid 2 VectorAdd "$fixtures/vector-x.tensor" "$fixtures/vector-y.tensor" "$work/vector.tensor"
reject --carrier fp32-basic --grid 2 Missing "$fixtures/vector-x.tensor" "$work/vector.tensor"
reject --carrier fp32-basic --grid 3 VectorAdd "$fixtures/vector-x.tensor" "$fixtures/vector-y.tensor" "$work/vector.tensor"
reject --carrier fp32-basic --grid 2 OnlineSoftmax "$fixtures/softmax-input.tensor" "$work/vector.tensor"
reject --carrier fp32-basic --grid 2 VectorAdd "$fixtures/vector-x.tensor" "$fixtures/softmax-input.tensor" "$work/vector.tensor"
reject --carrier fp32-basic --grid nope VectorAdd
reject --carrier fp32-basic --grid 2 VectorAdd "$fixtures/vector-x.tensor" "$work/vector.tensor"
python3 - "$fixtures/vector-x.tensor" "$work/uint32.tensor" <<'PYTHON'
import sys
from pathlib import Path
data = bytearray(Path(sys.argv[1]).read_bytes())
data[8] = 26  # valid uint32 tensor with the same width and shape
Path(sys.argv[2]).write_bytes(data)
PYTHON
reject --carrier fp32-basic --grid 2 VectorAdd "$work/uint32.tensor" "$fixtures/vector-y.tensor" "$work/vector.tensor"
head -c 17 "$fixtures/vector-x.tensor" > "$work/truncated.tensor"
reject --carrier fp32-basic --grid 2 VectorAdd "$work/truncated.tensor" "$fixtures/vector-y.tensor" "$work/vector.tensor"
cmp "$work/vector.tensor" "$fixtures/vector-sum.tensor"
mkdir "$work/destination"
reject --carrier fp32-basic --grid 2 VectorAdd "$fixtures/vector-x.tensor" "$fixtures/vector-y.tensor" "$work/destination"
shopt -s nullglob
leftovers=("$work"/destination.tmp.*)
(( ${#leftovers[@]} == 0 ))

# Compose the three actual SiLU stage executables from their predecessor's
# output files, and compare both intermediates and the final BF16 result.
mixed="$fixtures/tensor_examples"
silu=(--carrier binary64 --grid 2 --constexpr blockSize=2)
"$runner" "${silu[@]}" FusedSiLUGate "$mixed/silu-xReg.tensor" "$mixed/silu-gateReg.tensor" "$work/z.tensor"
cmp "$work/z.tensor" "$mixed/silu-zReg.tensor"
"$runner" "${silu[@]}" FusedSiLUActivation "$work/z.tensor" "$work/silu.tensor"
cmp "$work/silu.tensor" "$mixed/silu-siluReg.tensor"
"$runner" "${silu[@]}" FusedSiLUResidual "$work/silu.tensor" "$mixed/silu-residualReg.tensor" "$work/unfused.tensor"
cmp "$work/unfused.tensor" "$mixed/silu-outReg.tensor"

# Two result files become visible together. A failed repeat preserves both.
"$runner" --carrier binary64 --grid 1 --constexpr blockSize=4 --scalar rowStride=5 \
  Welford "$mixed/welford-row.tensor" "$work/stats"
cmp "$work/stats/meanReg.tensor" "$mixed/welford-mean.tensor"
cmp "$work/stats/varReg.tensor" "$mixed/welford-var.tensor"
reject --carrier binary64 --grid 1 --constexpr blockSize=4 --scalar rowStride=5 \
  Welford "$mixed/welford-row.tensor" "$work/stats"
reject --carrier binary64 --grid 2 --constexpr blockSize=4 --scalar rowStride=5 \
  Welford "$mixed/welford-row.tensor" "$work/invalid-stats"
reject --carrier binary64 --grid 1 --constexpr blockSize=4 \
  Welford "$mixed/welford-row.tensor" "$work/invalid-stats"
cmp "$work/stats/meanReg.tensor" "$mixed/welford-mean.tensor"
cmp "$work/stats/varReg.tensor" "$mixed/welford-var.tensor"
test ! -e "$work/invalid-stats"
leftovers=("$work"/stats.tmp.*)
(( ${#leftovers[@]} == 0 ))

# Source-rounded bindings enforce the actual launch extent, shapes and dtypes.
reject --carrier source-rounded --grid 1 --constexpr ncols=5 --constexpr BLOCK_N=4 \
  FusedSwiglu "$mixed/swiglu-x.tensor" "$mixed/swiglu-y.tensor" "$work/invalid-rounded.tensor"
reject --carrier source-rounded --grid 2 --constexpr ncols=6 --constexpr BLOCK_N=4 \
  FusedSwiglu "$mixed/swiglu-x.tensor" "$mixed/swiglu-y.tensor" "$work/invalid-rounded.tensor"
reject --carrier source-rounded --grid 2 --constexpr blockSize=4 \
  FloatDTypeSoftmax "$mixed/SoftmaxStable-output.tensor" "$work/invalid-rounded.tensor"
reject --carrier source-rounded --grid 2 --constexpr blockSize=4 \
  FloatDTypeSoftmax "$mixed/log-exp-input.tensor" "$work/invalid-rounded.tensor"
reject --carrier source-rounded --grid 2 --constexpr blockSize=4 \
  StableLogSumExp "$mixed/StableLogSumExp-input.tensor" "$work/invalid-rounded.tensor"
test ! -e "$work/invalid-rounded.tensor"

# Exercise spec declarations against the registry in this binary.
python3 tests/interp/check_example_bindings.py
