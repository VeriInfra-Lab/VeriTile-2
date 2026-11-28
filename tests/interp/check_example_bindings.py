"""Run examples whose qualified declaration exists but belongs to another binding."""
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


if __name__ == "__main__":
    main()
