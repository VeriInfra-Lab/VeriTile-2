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

The scan only sees warnings that Lean prints, and options and `#guard_msgs`
can hide them. `--sources` (one gate command) therefore matches what is being
hidden, not the ways of hiding it. It fails on
- the word `sorry` outside `#` comment lines of lakefile.toml and
  library/lakefile.toml (any spelling of the `warn.sorry` option);
- in a tests/lean source: the words `sorry` and `sorryAx` (also inside «»);
  `admit` and `stop` (which is `repeat sorry`) in tactic position; the
  `#guard_msgs` filters `drop warning` and `drop all`; a `#guard_msgs` whose
  expected-message docstring contains the word `warning`; and a
  `substring := true` guard whose filter does not name its severities, or
  names `warning` or `all`. A substring guard captures every message of its
  command, the `sorry` warning included, as soon as its docstring is a
  substring of the output, so `(error, substring := true)` is the only safe
  form: the warning then passes through to the log scan. The guard header
  (from the keyword to its `in`, across lines) may not contain a comment,
  since Lean reads a comment as whitespace and it would hide the filter from
  this check. Such a line passes
  only if its file is allowlisted and the line, or for a guard the next line,
  names the allowlisted declaration.
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


LAKEFILE_WORDS = re.compile(r'\bsorry\b')
TEST_WORDS = re.compile(r'\bsorry(?:Ax)?\b|\bdrop\s+(?:warning|all)\b')
# Tactic position only, outside `--` comments: `admit` and `stop` are also English words and names.
TACTICS = re.compile(r'(?:^|\bby\b|<;>|;|\(|·)\s*admit\b|(?:\bby\b|<;>|;|·)\s*stop\b|^\s*stop\s*$')
# A guard command starts a line or follows its docstring, which holds the messages it expects.
GUARD = re.compile(r'(?:/--((?:(?!-/).)*?)-/\s*|^[ \t]*)#guard_msgs\b', re.DOTALL | re.MULTILINE)
GUARD_END = re.compile(r'\bin\b')


def guard_header(text, start):
    """The text from just after `#guard_msgs` to its `in`."""
    end = GUARD_END.search(text, start)
    return text[start:end.start() if end else len(text)]


def guard_options(header):
    """The filter options of a comment-free guard header, or None."""
    flat = ' '.join(header.split())
    return flat[1:flat.index(')')] if flat.startswith('(') and ')' in flat else None


def captures_warnings(options):
    """Whether a substring guard with these filter options can swallow a warning."""
    items = [item.strip() for item in (options or '').split(',')]
    if not any(re.fullmatch(r'substring\s*:=\s*true', item) for item in items):
        return False
    severities = [item for item in items if item and ':=' not in item]
    return not severities or any(re.search(r'\b(?:warning|all)\b', item) for item in severities)


def tripwires(root, accepted):
    """Source lines that use or could hide a `sorry` outside the allowlist."""
    hits = []
    for name in ('lakefile.toml', 'library/lakefile.toml'):
        path = root / name
        lines = path.read_text(errors='replace').splitlines() if path.is_file() else []
        hits += [f'{name}:{number}: {match.group(0)}' for number, line in enumerate(lines, 1)
                 if not line.lstrip().startswith('#') for match in LAKEFILE_WORDS.finditer(line)]
    for path in sorted((root / 'tests/lean').rglob('*.lean')):
        file = path.relative_to(root).as_posix()
        names = {name for f, name in accepted if f == file}
        text = path.read_text(errors='replace')
        lines = text.splitlines()

        def named(*texts):
            return any(re.search(r'(?<![\w.])' + re.escape(name) + r'(?![\w.])', t) for name in names for t in texts)
        for number, line in enumerate(lines, 1):
            if not named(line):
                hits += [f'{file}:{number}: {match.group(0).strip()}' for match in
                         [*TEST_WORDS.finditer(line), *TACTICS.finditer(line.split('--')[0])]]
        for match in GUARD.finditer(text):
            number = text.count('\n', 0, match.end()) + 1
            if named(*lines[number - 1:number + 1]):
                continue
            if match.group(1) and re.search(r'\bwarning\b', match.group(1), re.IGNORECASE):
                hits.append(f'{file}:{number}: #guard_msgs expecting a warning')
            header = guard_header(text, match.end())
            if '/-' in header or '--' in header:
                hits.append(f'{file}:{number}: comment in a #guard_msgs header')
            elif captures_warnings(guard_options(header)):
                hits.append(f'{file}:{number}: #guard_msgs ({guard_options(header)}) can swallow warnings; '
                            'name the severities, e.g. (error, substring := true)')
    return hits


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('logs', nargs='*', type=Path, help='output of gate commands')
    parser.add_argument('--allowlist', type=Path, default=ALLOWLIST)
    parser.add_argument('--sources', action='store_true', help='check the sources for ways to hide the warning')
    parser.add_argument('--root', type=Path, default=ROOT, help=argparse.SUPPRESS)
    args = parser.parse_args()
    if args.sources:
        hits = tripwires(args.root, allowed(args.allowlist))
        if hits:
            raise ValueError('a source uses or can hide sorry outside the allowlist:\n' + '\n'.join(hits))
        print('[ok] no lakefile or tests/lean source uses or hides sorry outside the allowlist')
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
