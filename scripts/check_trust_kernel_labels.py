#!/usr/bin/env python3
"""Check the elaborated trust registry against §7 and the source census."""
import csv
import json
from pathlib import Path
import re
import subprocess
import sys


from check_fork_target import ROOT, TARGETS, sources


REGISTRY = '''
open Lean Meta Elab Command VeriTile.Dist

-- Read the actual registry, including persistent attribute registrations. Open
-- metadata parameters symbolically so inspecting a label needs no sample input.
run_cmd do
  let entries ← liftCoreM registeredTrustAssumptions
  for entry in entries do
    let labels ← liftTermElabM <| withTransparency .all do
      let metadata ← mkConstWithFreshMVarLevels entry.metadata
      forallTelescopeReducing (← inferType metadata) fun args _ => do
        let mut xs ← mkAppM ``TrustAssumption.affectedKernels #[mkAppN metadata args]
        let mut labels : Array String := #[]
        repeat
          let list ← whnf xs
          if list.isAppOf ``List.nil then break
          unless list.isAppOfArity ``List.cons 3 do
            throwError "{entry.name}: cannot enumerate affectedKernels: {list}"
          let fields := list.getAppArgs
          let some label := getStringValue? (← whnf fields[1]!)
            | throwError "{entry.name}: affected kernel label is not a fixed string"
          labels := labels.push label
          xs := fields[2]!
        return labels
    IO.println ("KERNEL-LABELS " ++ (toJson (entry.name.toString, labels)).compress)
'''


def documented_labels():
    sources = (ROOT / "documents/dist/PrimitiveSources.md").read_text()
    section = sources.split("\n## 7. Named assumptions\n", 1)[1].split("\n## ", 1)[0]
    labels = set()
    for row in section.splitlines():
        if not row.startswith("| Affected kernels |"):
            continue
        labels.update(re.findall(r"\bK\d+\b", row))
        for first, last in re.findall(r"\bK(\d+) to K(\d+)\b", row):
            labels.update(f"K{i}" for i in range(int(first), int(last) + 1))
        for number, name in re.findall(r"\b(D\d+) `(\w+)`", row):
            labels.update((f"{number} {name}", name))
        if "K-M" in row:
            labels.update(f"K-M {n}" for n in re.findall(r"\[(D\d+) ", row))
        # Some files occur only in §7, including the specialized TileScale
        # examples. Preserve the front end attached to that part of the prose.
        prose = re.sub(r"\]\([^)]*\)", "]", row)
        parts = re.split(r"\b(Triton-distributed|TileScale)\b", prose)
        for frontend, clause in zip(parts[1::2], parts[2::2]):
            for name in re.findall(r"`(?:[\w./-]+/)?([\w.-]+\.py)`", clause):
                labels.update((f"{frontend} {name}", name))

    with (ROOT / "scripts/census/targets.tsv").open() as targets:
        for _, frontend, _, _, path, _ in csv.reader(
                (line for line in targets if line.strip() and not line.startswith("#")), delimiter="\t"):
            if not path:
                continue
            name = Path(path).name
            labels.update((path, name, f"{frontend} {name}"))
            tutorial = re.fullmatch(r"tutorials/(\d+)-[\w-]+\.py", path)
            if tutorial:
                labels.add(f"{frontend} tutorial {tutorial[1]}")

    census = (ROOT / "documents/census/MinimalSyntax.md").read_text()
    for match in re.finditer(r"^### ([^\n:]+): kernels\n([\s\S]*?)(?=^###? |\Z)", census, re.M):
        for line in match[2].splitlines():
            if re.match(r"^\| \d+ \|", line):
                _, _, _, _, path, name, _, _ = (cell.strip().strip("`") for cell in line.split("|"))
                labels.update((name, f"{match[1]} {name}", f"{match[1]} {Path(path).name}"))
    return labels


def main():
    known = documented_labels()
    # Lake's fork libraries include submodules independently of root imports.
    paths = [p for directory in TARGETS.values() for p in sources(directory)]
    imports = ["import " + ".".join(p.relative_to(ROOT).with_suffix("").parts) for p in paths]
    process = subprocess.run(["lake", "env", "lean", "--stdin"], input="\n".join(imports) + REGISTRY,
                             cwd=ROOT, capture_output=True, text=True)
    if process.returncode:
        sys.stderr.write(process.stdout + process.stderr)
        return process.returncode
    entries = [json.loads(line.removeprefix("KERNEL-LABELS ")) for line in process.stdout.splitlines()
               if line.startswith("KERNEL-LABELS ")]
    if not entries:
        raise ValueError("no trust registrations returned")
    missing = [(entry, label) for entry, labels in entries for label in labels if label not in known]
    for entry, label in missing:
        print(f"{entry}: unknown affected kernel {label!r}", file=sys.stderr)
    if missing:
        return 1
    print(f"Checked {sum(len(labels) for _, labels in entries)} kernel labels in {len(entries)} trust registrations.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
