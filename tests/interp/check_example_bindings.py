"""Exercise file-runner and example-spec binding mismatches through the driver."""
import json
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
EXAMPLES = ROOT / "experiments/interp_gpu/specs/examples"


def main():
    def spec(name):
        return json.loads((EXAMPLES / (name + ".json")).read_text())

    original = spec("LogExp")["kernel"]["lean"]
    optimized = spec("LogExpOptimized")["kernel"]["lean"]
    row_max = spec("RowWiseMax")["kernel"]["lean"]
    cases = [("LogExp", optimized), ("LogExpOptimized", original),
             ("RowWiseMax", row_max.rsplit(".", 1)[0] + ".inlinedKernel")]
    for name, replacement in cases:
        document = spec(name)
        correct = document["kernel"]["lean"]
        document["kernel"]["lean"] = replacement
        with tempfile.TemporaryDirectory() as work:
            mutant = Path(work) / (name + ".json")
            mutant.write_text(json.dumps(document))
            run = subprocess.run(["uv", "run", "--no-project", "--python", "3.11", "--script",
                                  str(EXAMPLES / "run.py"), str(mutant)],
                                 cwd=ROOT, capture_output=True, text=True)
            expected = f"{name}: kernel.lean must name the registered mirror source {correct}, got {replacement}"
            if run.returncode != 1 or expected not in run.stderr:
                raise SystemExit(f"{name}: expected a registration mismatch; got {run.returncode}\n{run.stderr}")
        print(f"{name}: rejected {replacement}", flush=True)

    runner = ROOT / ".lake/build/bin/veritile-run"
    bindings = json.loads(subprocess.check_output([runner, "--example-sources"]))
    bindings["MissingExample"] = bindings["VectorAdd"]
    with tempfile.TemporaryDirectory() as work:
        extra = Path(work) / "extra-runner"
        extra.write_text("#!/usr/bin/env python3\nimport sys\n"
                         "assert sys.argv[1:] == ['--example-sources']\n"
                         f"print({json.dumps(bindings)!r})\n")
        extra.chmod(0o755)
        run = subprocess.run(["uv", "run", "--no-project", "--python", "3.11", "--script",
                              str(EXAMPLES / "run.py"), "--runner", str(extra)],
                             cwd=ROOT, capture_output=True, text=True)
        expected = "file-runner bindings without an example spec: MissingExample"
        if run.returncode != 1 or run.stderr.strip().splitlines()[-1:] != [expected]:
            raise SystemExit(f"expected the missing-spec diagnostic, got {run.returncode}\n{run.stderr}")
        print(expected, flush=True)


if __name__ == "__main__":
    main()
