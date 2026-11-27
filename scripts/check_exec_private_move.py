#!/usr/bin/env python3
"""Compare the five list-m rows for #48 in built pre- and post-move checkouts."""
import argparse
import hashlib
from pathlib import Path
import subprocess
import tempfile

from check_frozen_statements import DEFINITION_HEADER, LEAN, read

OLD = "_private.VeriTile.Staging.Dist.JudgmentSpec.0."
NEW = "_private.VeriTile.Dist.Exec.0."
HELPERS = ("bumpMem", "deliverMemory", "deliverMemory.match_1")
CONSTRUCTORS = ("VeriTile.Dist.Fire.bump", "VeriTile.Dist.step.deliver")


def entries(checkout, prefix):
    names = {*CONSTRUCTORS, *(prefix + "VeriTile.Dist." + h for h in HELPERS)}
    literals = ", ".join('"' + name + '"' for name in sorted(names))
    query = f'''
run_cmd do
  let env ← getEnv
  let wanted : List String := [{literals}]
  for (n, info) in env.constants.toList do
    if wanted.contains n.toString then
      liftIO <| IO.println s!"ROW\\t{{n}}\\t{{(frozenEntry info).1}}"
'''
    with tempfile.TemporaryDirectory() as tmp:
        probe = Path(tmp) / "ExecRows.lean"
        probe.write_text("import Lean\nimport VeriTile.Staging.Dist.JudgmentSpec\n" + LEAN + query)
        output = subprocess.check_output(["lake", "env", "lean", str(probe)], cwd=checkout, text=True)
    result = {}
    for line in output.splitlines():
        if line.startswith("ROW\t"):
            _, name, value = line.split("\t", 2)
            result[name] = value.encode()
    if result.keys() != names:
        raise ValueError(f"expected the five #48 rows at {checkout}, found {sorted(result)}")
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("before", type=Path)
    parser.add_argument("after", type=Path)
    args = parser.parse_args()
    table = args.before / "documents/dist/FrozenDefinitions.tsv"
    _, rows = read(table, DEFINITION_HEADER)
    recorded = dict(rows.values())
    before = entries(args.before, OLD)
    after = entries(args.after, NEW)
    for old_name, old_bytes in sorted(before.items()):
        if hashlib.sha256(old_bytes).hexdigest() != recorded[old_name]:
            raise ValueError(f"{old_name}: the baseline differs from its recorded fingerprint")
        new_name = old_name.replace(OLD, NEW)
        normalized = old_bytes.replace(OLD.encode(), NEW.encode())
        if after[new_name] != normalized:
            raise ValueError(f"{new_name}: differs after the permitted private-prefix substitution")
        print(f"{new_name}\t{hashlib.sha256(normalized).hexdigest()}\tbyte-identical")


if __name__ == "__main__":
    main()
