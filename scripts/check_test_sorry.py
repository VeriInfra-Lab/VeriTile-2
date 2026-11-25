#!/usr/bin/env python3
"""Fail on `declaration uses 'sorry'` in a tests/lean file, unless allowlisted.

A `sorry` in a test certificate is only a warning to Lean and Lake, and the
environment audit of check_fork_target.py cannot see it in an `example`,
which leaves no constant behind. scripts/local_gate.sh therefore runs this
check on the output of every gate command: the warnings of `lake env lean
tests/lean/...` and those Lake replays for every tests/lean module it builds
or finds cached.

scripts/test-sorry-allowlist.txt lists the accepted cases, one per line:
`file<TAB>declaration<TAB>reason`. The declaration is the word at the reported
position: the name of a theorem or definition, or `example`.

The scan only sees warnings that Lean prints. `--sources` (one gate command)
fails when `warn.sorry` appears in lakefile.toml, library/lakefile.toml or a
tests/lean source, since that option turns the warning off, or when
`declaration uses` appears in a tests/lean source, since `#guard_msgs` can
swallow the warning.
"""
import argparse
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
ALLOWLIST = ROOT / 'scripts/test-sorry-allowlist.txt'
# Lake prints `warning: FILE:L:C: MSG`, Lean prints `FILE:L:C: warning: MSG`; this toolchain quotes with backticks.
# FILE is anchored to this repository's tests/lean, not a dependency's under .lake/packages.
WARNING = re.compile(r'^(?:warning: )?(?:\./|' + re.escape(str(ROOT)) + r'/)?(tests/lean/[^\s:]+\.lean):(\d+):(\d+): '
                     r'(?:warning: )?declaration uses .sorry.', re.MULTILINE)


def allowed(path):
    entries = set()
    for number, line in enumerate(path.read_text().splitlines(), 1):
        if not line.strip() or line.startswith('#'):
            continue
        fields = line.split('\t')
        if len(fields) != 3 or not all(field.strip() for field in fields):
            raise ValueError(f'{path.name}:{number}: expected file<TAB>declaration<TAB>reason')
        entries.add((fields[0], fields[1]))
    return entries


def declaration(file, line, column):
    """The word at a reported position, or `?` if the file is not in this checkout."""
    source = ROOT / file
    lines = source.read_text().splitlines() if source.is_file() else []
    word = re.match(r'[^\s(){}\[\]:]+', lines[line - 1][column:]) if line <= len(lines) else None
    return word.group(0) if word else '?'


def tripwires(root):
    """Source lines that could hide a `sorry` warning from the scan."""
    hits = []
    sources = [(root / name, ('warn.sorry',)) for name in ('lakefile.toml', 'library/lakefile.toml')]
    sources += [(path, ('warn.sorry', 'declaration uses')) for path in sorted((root / 'tests/lean').rglob('*.lean'))]
    for path, words in sources:
        if not path.is_file():
            continue
        for number, line in enumerate(path.read_text(errors='replace').splitlines(), 1):
            hits += [f'{path.relative_to(root)}:{number}: {word}' for word in words if word in line]
    return hits


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('logs', nargs='*', type=Path, help='output of gate commands')
    parser.add_argument('--allowlist', type=Path, default=ALLOWLIST)
    parser.add_argument('--sources', action='store_true', help='check the sources for ways to hide the warning')
    parser.add_argument('--root', type=Path, default=ROOT, help=argparse.SUPPRESS)
    args = parser.parse_args()
    if args.sources:
        hits = tripwires(args.root)
        if hits:
            raise ValueError('a source can hide `declaration uses sorry` from the gate:\n' + '\n'.join(hits))
        print('[ok] no lakefile or tests/lean source mentions warn.sorry or `declaration uses`')
    accepted = allowed(args.allowlist)
    found = set()
    for log in args.logs:
        for match in WARNING.finditer(log.read_text(errors='replace')):
            file, line, column = match.group(1), int(match.group(2)), int(match.group(3))
            found.add((file, declaration(file, line, column), f'{file}:{line}:{column}'))
    rejected = sorted(f'SORRY\t{file}\t{name}\t({where})' for file, name, where in found
                      if (file, name) not in accepted)
    if rejected:
        raise ValueError(f'tests/lean uses sorry outside {args.allowlist.name}:\n' + '\n'.join(rejected))


if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError) as error:
        print(f'[FAIL] {error}', file=sys.stderr)
        raise SystemExit(1)
