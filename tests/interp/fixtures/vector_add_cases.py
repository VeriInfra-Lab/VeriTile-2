"""Regenerate the independently encoded input and expected FP32 tensors for #645."""
import argparse
from pathlib import Path
import struct
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parents[2] / "scripts"))
from interp.tensorfile import Tensor


def fixture_bytes(values):
    return Tensor("fp32", (len(values),), struct.pack(f"<{len(values)}f", *values)).to_bytes()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    cases = [
        ("flat-add", [2.5, -1.25, 7, 12.5, -6], [0.75, 5, -3.5, -12, 0.5]),
        ("float-add", [2**24, -(2**24), -0.0, -1.25, 9.5, -3], [1, -1, -0.0, 2.75, -11.25, 3]),
    ]
    for name, x, y in cases:
        # All operands and the exact sums fit binary64; struct rounds to binary32.
        for suffix, values in [("x", x), ("y", y), ("sum", [a + b for a, b in zip(x, y)])]:
            path = HERE / f"{name}-{suffix}.tensor"
            data = fixture_bytes(values)
            if args.check:
                if path.read_bytes() != data:
                    raise SystemExit(f"incorrect independent fixture: {path}")
            else:
                path.write_bytes(data)


if __name__ == "__main__":
    main()
