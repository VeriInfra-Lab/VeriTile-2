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
