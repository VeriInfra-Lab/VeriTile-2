# /// script
# requires-python = ">=3.10"
# dependencies = ["jsonschema==4.25.1"]
# ///
"""Run a file-backed example through the normal veritile-run entry point."""
import argparse
import ast
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile

from jsonschema import Draft7Validator, ValidationError

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
sys.path.insert(0, str(ROOT / "scripts"))
from interp import tensorfile


def check_kernel(kernel, arguments, registered_sources):
    source, function = kernel["source"].rsplit("::", 1)
    path = Path(source)
    if path.is_absolute() or not (ROOT / path).resolve().is_relative_to(ROOT):
        raise ValueError(f"{kernel['name']}: kernel.source must be repository-relative: {source}")
    if not (ROOT / path).is_file():
        raise ValueError(f"{kernel['name']}: kernel.source file does not exist: {source}")
    module = ast.parse((ROOT / path).read_text(), filename=source)
    functions = [node for node in module.body if isinstance(node, ast.FunctionDef) and node.name == function]
    decorators = [dec.func if isinstance(dec, ast.Call) else dec
                  for node in functions for dec in node.decorator_list]
    if not any(ast.unparse(dec) == "triton.jit" for dec in decorators):
        raise ValueError(f"{kernel['name']}: kernel.source is not a top-level @triton.jit function: {kernel['source']}")

    runtime = [arg.arg for arg in functions[0].args.args
               if not arg.annotation or ast.unparse(arg.annotation) != "tl.constexpr"]
    if runtime != [arg["parameter"] for arg in arguments]:
        raise ValueError(f"{kernel['name']}: runtime arguments must follow the source order {runtime}")

    # Lean declaration namespaces use VeriTile.Bench.Examples, while Lake module
    # paths for these mirrors start at bench/examples. Resolve the actual
    # declaration in the compiled environment, including its declared name.
    name = kernel["lean"]
    registered = registered_sources.get(kernel["name"])
    if registered is None:
        raise ValueError(f"{kernel['name']}: no such file-runner registration")
    if name != registered:
        raise ValueError(f"{kernel['name']}: kernel.lean must name the registered mirror source "
                         f"{registered}, got {name}")
    prefix = "VeriTile.Bench.Examples."
    parts = name.removeprefix(prefix).split(".")
    if not name.startswith(prefix) or len(parts) < 2 or not all(
            re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", part) for part in parts):
        raise ValueError(f"{kernel['name']}: invalid qualified kernel.lean example name: {name}")
    # Kernel definitions may live directly in the family's namespace even
    # though the actual module is the family's Kernels.lean (e.g. LogExp).
    module_path = Path("bench", "examples", *parts[:-1]) if len(parts) > 2 else Path(
        "bench", "examples", parts[0], "Kernels")
    if not (ROOT / module_path.with_suffix(".lean")).is_file():
        raise ValueError(f"{kernel['name']}: kernel.lean file does not exist: {module_path}.lean")
    if path.parent != module_path.parent:
        raise ValueError(f"{kernel['name']}: kernel.lean and kernel.source name different example directories")
    lookup = f"import {'.'.join(module_path.parts)}\n#check @{name}\n"
    checked = subprocess.run(["lake", "env", "lean", "--stdin"], cwd=ROOT, input=lookup,
                             capture_output=True, text=True)
    if checked.returncode:
        raise ValueError(f"{kernel['name']}: kernel.lean lookup failed for {name}: "
                         + (checked.stdout + checked.stderr).strip())


def check_layout(path, descriptor):
    tensor = tensorfile.read(path)
    if (tensor.dtype, list(tensor.shape)) != (descriptor["dtype"], descriptor["shape"]):
        raise ValueError(f"{path}: dtype or shape differs from the spec")


def run_case(spec, case, runner, work):
    kernel = spec["kernel"]["name"]
    outputs = spec["output_buffers"]
    names = [out["name"] for out in outputs]
    inputs = case["inputs"]
    ports = [arg["buffer"] for arg in spec["arguments"] if "buffer" in arg]
    if (len(set(ports)) != len(ports) or len(set(names)) != len(names)
            or set(ports) != inputs.keys() | set(names) or set(names) != case["expected"].keys()):
        raise ValueError(f"{kernel}: file arguments must match all declared inputs and outputs")
    input_ports = [port for port in ports if port in inputs]
    if not input_ports:
        raise ValueError(f"{kernel}: at least one input is required")
    paths = [ROOT / inputs[port]["file"] for port in input_ports]
    for port, path in zip(input_ports, paths):
        check_layout(path, inputs[port])
    # These bindings derive their constexpr from the first input shape.
    # Reject stale specializations even if the runner could execute a different one.
    shape = inputs[input_ports[0]]["shape"]
    grid = spec["grid"]
    if kernel == "VectorAdd" and (grid[0] == 0 or spec["constexpr"] != {"BLOCK_SIZE": shape[0] // grid[0]}):
        raise ValueError("VectorAdd: BLOCK_SIZE must match the block bound by the registry")
    if kernel == "OnlineSoftmax" and spec["constexpr"] != {"N": shape[-1]}:
        raise ValueError("OnlineSoftmax: N must match the row width bound by the registry")
    flags = []
    if kernel not in ("VectorAdd", "OnlineSoftmax"):
        for key, value in spec["constexpr"].items():
            flags.extend(["--constexpr", f"{key}={value}"])
    for arg in spec["arguments"]:
        if "value" in arg:
            flags.extend(["--scalar", f"{arg['parameter']}={arg['value']}"])
    destination = work / ("result.tensor" if len(outputs) == 1 else "results")
    subprocess.run([runner, "--carrier", spec["launch"]["carrier"], "--grid",
                    ",".join(map(str, grid)), *flags, kernel, *paths, destination], check=True)
    if len(outputs) > 1 and {p.name for p in destination.iterdir()} != {name + ".tensor" for name in names}:
        raise ValueError(f"{kernel}: result files differ from declared outputs")
    for out in outputs:
        name = out["name"]
        actual = destination if len(outputs) == 1 else destination / (name + ".tensor")
        check_layout(actual, out)
        expected = ROOT / case["expected"][name]
        check_layout(expected, out)
        if actual.read_bytes() != expected.read_bytes():
            raise ValueError(f"{kernel}: output {name} differs from {expected}")
        print(f"{kernel} {case['class']} {name} {tensorfile.read(actual).sha256()}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("spec", type=Path, nargs="*", help="defaults to all example JSON files")
    parser.add_argument("--runner", type=Path, default=ROOT / ".lake/build/bin/veritile-run")
    args = parser.parse_args()
    validator = Draft7Validator(json.loads((HERE.parent / "schema.json").read_text()))
    runner = args.runner.resolve()
    try:
        registered_sources = json.loads(subprocess.check_output(
            [runner, "--example-sources"], text=True))
        if not isinstance(registered_sources, dict):
            raise ValueError("expected a JSON object of file-runner bindings")
    except (OSError, ValueError, subprocess.CalledProcessError) as exc:
        parser.exit(1, f"cannot read example bindings from {runner}: {exc}\n")
    specs = []
    for path in args.spec or sorted(HERE.glob("*.json")):
        try:
            spec = json.loads(path.read_text())
            validator.validate(spec)
            specs.append((path, spec))
        except (ValueError, OSError, ValidationError) as exc:
            parser.exit(1, f"{path}: {exc}\n")
    if not args.spec:
        missing = sorted(registered_sources.keys() - {spec["kernel"]["name"] for _, spec in specs})
        if missing:
            parser.exit(1, "file-runner bindings without an example spec: " + ", ".join(missing) + "\n")
    for path, spec in specs:
        try:
            check_kernel(spec["kernel"], spec["arguments"], registered_sources)
            for case in spec["input_classes"]:
                with tempfile.TemporaryDirectory(prefix="veritile-spec-") as work:
                    run_case(spec, case, runner, Path(work))
        except (ValueError, OSError, SyntaxError, ValidationError, subprocess.CalledProcessError) as exc:
            parser.exit(1, f"{path}: {exc}\n")


if __name__ == "__main__":
    main()
