#!/usr/bin/env python3
"""Verify the entire signed closure before and after the #48 module move (decision v)."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tempfile

from check_frozen_statements import DEFINITION_HEADER, LEAN, STATEMENT_HEADER, read


DIST = "VeriTile.Dist."
OLD_PRIVATE = "_private.VeriTile.Staging.Dist.JudgmentSpec.0." + DIST
NEW_PRIVATE = "_private.VeriTile.Dist.Exec.0." + DIST
PRIVATE = {NEW_PRIVATE + name: OLD_PRIVATE + name
           for name in ("bumpMem", "deliverMemory", "deliverMemory.match_1")}
AUX = {DIST + after: DIST + before for after, before in (
    ("ReadsFrom.match_1", "Machine.count?.match_1"),
    ("ReadsFrom._sparseCasesOn_1", "Machine.count?._sparseCasesOn_1"),
    ("Occurrence.onlyAddsTo.match_1", "Occurrence.event?.match_1"),
)}
MOVED = PRIVATE | AUX
# A literal may contain text that looks like a constant. Skip the whole quoted
# literal and rewrite only a complete constant token in the official serialization.
TOKENS = re.compile(r'"(?:\\.|[^"\\])*"|\(C ([^ ]+) (?=\[)')


def normalize(serialized):
    def rename(match):
        name = match[1]
        return "(C " + MOVED[name] + " " if name in MOVED else match[0]
    return TOKENS.sub(rename, serialized)


def digest(text):
    return hashlib.sha256(text.encode()).hexdigest()


def capture(checkout, rows):
    imports = "".join(f"import {name}\n" for name in sorted({r[1] for r in rows}))
    query = "#frozenStatements [" + ", ".join(json.dumps(r[0]) for r in rows) + "]\n"
    with tempfile.TemporaryDirectory() as tmp:
        probe = Path(tmp) / "ExecRows.lean"
        probe.write_text("import Lean\n" + imports + LEAN + query)
        result = subprocess.check_output(["lake", "env", "lean", str(probe)], cwd=checkout, text=True)
    statements, definitions = {}, {}
    for line in result.splitlines():
        if line.startswith("D\t"):
            _, name, definitions_text = line.split("\t", 2)
            definitions[name] = definitions_text
        elif line.startswith("S\t"):
            _, name, module, text = line.split("\t", 3)
            statements[name] = (module, digest(text))
    signed = {name: (module, sha) for name, module, sha, _ in rows}
    if statements != signed:
        raise ValueError("signed statement inventory, owner or type changed")
    return definitions


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("before", type=Path)
    parser.add_argument("after", type=Path)
    args = parser.parse_args()
    directory = Path("documents/dist")
    for name in ("FrozenStatements.tsv", "FrozenDefinitions.tsv"):
        if (args.before / directory / name).read_bytes() != (args.after / directory / name).read_bytes():
            raise ValueError(f"{name}: signed table changed")
    _, rows = read(args.before / directory / "FrozenStatements.tsv", STATEMENT_HEADER)
    _, signed = read(args.before / directory / "FrozenDefinitions.tsv", DEFINITION_HEADER)
    before = capture(args.before, rows.values())
    if {name: digest(raw) for name, raw in before.items()} != dict(signed.values()):
        raise ValueError("baseline definitions differ from the signed table")
    after = capture(args.after, rows.values())
    expected = (before.keys() - PRIVATE.values()) | MOVED.keys()
    missing, extra = sorted(expected - after.keys()), sorted(after.keys() - expected)
    if missing or extra:
        raise ValueError(f"unexpected definition inventory; missing {missing}, extra {extra}")
    for name, raw in sorted(after.items()):
        original = MOVED.get(name, name)
        if name == original and raw == before[original]:
            continue
        if normalize(raw) != before[original]:
            raise ValueError(f"{name}: content differs from signed {original} after decision-v renames")
        print(f"{name} -> {original}\t{digest(before[original])}\tbyte-identical")
    print(f"{len(rows)} signed statements; {len(before)} baseline and {len(after)} post-move definitions verified")


if __name__ == "__main__":
    main()
