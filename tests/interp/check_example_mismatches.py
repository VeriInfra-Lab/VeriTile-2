"""Change one expected data bit per port and run its unmodified public spec client."""
import json
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
SPECS = ROOT / "experiments/interp_gpu/specs/examples"


def main():
    for path in sorted(SPECS.glob("*.json")):
        original = json.loads(path.read_text())
        if original["launch"]["carrier"] not in ("binary64", "source-rounded"):
            continue
        for index, case in enumerate(original["input_classes"]):
            for port, fixture in case["expected"].items():
                with tempfile.TemporaryDirectory() as temp:
                    folder = Path(temp)
                    changed = bytearray((ROOT / fixture).read_bytes())
                    changed[-1] ^= 1
                    wrong = folder / "wrong.tensor"
                    wrong.write_bytes(changed)
                    spec = json.loads(path.read_text())
                    spec["input_classes"][index]["expected"][port] = str(wrong)
                    mutant = folder / path.name
                    mutant.write_text(json.dumps(spec))
                    run = subprocess.run(["uv", "run", "--no-project", "--python", "3.11", "--script",
                                          str(SPECS / "run.py"), str(mutant)], cwd=ROOT,
                                         capture_output=True, text=True)
                    if run.returncode != 1 or f"output {port} differs from {wrong}" not in run.stderr:
                        raise SystemExit(f"{path.name} {port}: wrong outcome {run.returncode}\n{run.stderr}")
                    print(f"{path.stem} {port}: one-bit mismatch rejected (exit 1)", flush=True)


if __name__ == "__main__":
    main()
