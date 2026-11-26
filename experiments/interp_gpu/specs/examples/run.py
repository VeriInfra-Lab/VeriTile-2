"""Run a file-backed example through the normal veritile-run entry point."""
import argparse
import json
from pathlib import Path
import subprocess
import sys
import tempfile

from jsonschema import Draft7Validator

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
sys.path.insert(0, str(ROOT / "scripts"))
from interp import tensorfile


def check_layout(path, descriptor):
    tensor = tensorfile.read(path)
    if (tensor.dtype, list(tensor.shape)) != (descriptor["dtype"], descriptor["shape"]):
        raise ValueError(f"{path}: dtype or shape differs from the spec")


def run_case(spec, case, runner, work):
    kernel = spec["kernel"]["name"]
    output, = spec["output_buffers"]
    inputs = case["inputs"]
    ports = [arg["buffer"] for arg in spec["arguments"]]
    if (len(ports) != len(inputs) + 1 or set(ports[:-1]) != inputs.keys()
            or ports[-1] != output["name"] or case["expected"].keys() != {output["name"]}):
        raise ValueError(f"{kernel}: file runner requires ordered inputs followed by one output")
    paths = [ROOT / inputs[port]["file"] for port in ports[:-1]]
    for port, path in zip(ports, paths):
        check_layout(path, inputs[port])
    # These bindings derive their constexpr from the first input shape.
    # Reject stale specializations even if the runner could execute a different one.
    shape = inputs[ports[0]]["shape"]
    grid = spec["grid"]
    if kernel == "VectorAdd" and (grid[0] == 0 or spec["constexpr"] != {"BLOCK_SIZE": shape[0] // grid[0]}):
        raise ValueError("VectorAdd: BLOCK_SIZE must match the block bound by the registry")
    if kernel == "OnlineSoftmax" and spec["constexpr"] != {"N": shape[-1]}:
        raise ValueError("OnlineSoftmax: N must match the row width bound by the registry")
    destination = work / "result.tensor"
    subprocess.run([runner, "--carrier", spec["launch"]["carrier"], "--grid",
                    ",".join(map(str, grid)), kernel, *paths, destination], check=True)
    check_layout(destination, output)
    expected = ROOT / case["expected"][output["name"]]
    if destination.read_bytes() != expected.read_bytes():
        raise ValueError(f"{kernel}: output differs from {expected}")
    print(f"{kernel} {case['class']} {output['name']} {tensorfile.read(destination).sha256()}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("spec", type=Path, nargs="*", help="defaults to all example JSON files")
    parser.add_argument("--runner", type=Path, default=ROOT / ".lake/build/bin/veritile-run")
    args = parser.parse_args()
    validator = Draft7Validator(json.loads((HERE.parent / "schema.json").read_text()))
    for path in args.spec or sorted(HERE.glob("*.json")):
        spec = json.loads(path.read_text())
        validator.validate(spec)
        for case in spec["input_classes"]:
            with tempfile.TemporaryDirectory(prefix="veritile-spec-") as work:
                run_case(spec, case, args.runner.resolve(), Path(work))


if __name__ == "__main__":
    main()
