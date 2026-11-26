#!/usr/bin/env python3
"""Reject unapproved sorry warnings, axiom declarations and printed dependencies in tests/lean.

A `sorry` in a test certificate is only a warning to Lean and Lake, and the
environment audit of check_fork_target.py cannot see it in an `example`,
which leaves no constant behind. scripts/local_gate.sh therefore runs this
check on the output of every gate command: the warnings of `lake env lean
tests/lean/...` and those Lake replays for every tests/lean module it builds
or finds cached.

Source checks also reject a test's own axiom declarations. Log checks audit
the dependencies reported by `#print axioms` at test sites. Lake supplies
the site in its log; direct Lean runs supply the test file on the command line.

scripts/test-sorry-allowlist.txt uses `file<TAB>declaration<TAB>reason`.
For a source axiom use the name as written, including any quoting or namespace
prefix. For a sorry warning use the word at the reported position (or `example`).
To permit sorryAx in printed dependencies use the fully qualified name printed
for the audited declaration. An allowed source axiom still fails as a dependency.

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
  substring of the output; with the severities named, as in
  `(error, substring := true)`, the warning passes through to the log scan
  instead. The guard header
  (from the keyword to its `in`, across lines) may not contain a comment,
  since Lean reads a comment as whitespace and it would hide the filter from
  this check. Such a line passes
  only if its file is allowlisted and the line, or for a guard the next line,
  names the allowlisted declaration.
- in a tests/lean source: command-level metaprogramming (`macro`,
  `macro_rules`, `syntax`, `elab`, `elab_rules`, `notation`, `infix`,
  `infixl`, `infixr`, `prefix`, `postfix`) unless the file and the declared
  name are in scripts/test-metaprogram-allowlist.txt, since a metaprogram can
  assemble a hiding guard or a `sorry` out of pieces no rule here sees.
Guards and metaprograms are found anywhere in code, not only at a line start;
`--` and `/- -/` comments (which nest) and string contents are skipped, and
docstrings are kept for the guard rules. What remains needs metaprogramming
defined outside tests/lean, which coordinator review of gate-file and
allowlist diffs covers.
"""
import argparse
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
ALLOWLIST = ROOT / 'scripts/test-sorry-allowlist.txt'
# Kept apart from ALLOWLIST: an accepted macro name must not exempt the lines that use it from the sorry rules.
META_ALLOWLIST = ROOT / 'scripts/test-metaprogram-allowlist.txt'
# Lake prints `warning: FILE:L:C: MSG`, Lean prints `FILE:L:C: warning: MSG`; this toolchain quotes with backticks.
# FILE is anchored to this repository's tests/lean, not a dependency's under .lake/packages.
WARNING = re.compile(r'^(?:warning: )?(?:\./|' + re.escape(str(ROOT)) + r'/)?(tests/lean/[^\s:]+\.lean):(\d+):(\d+): '
                     r'(?:warning: )?declaration uses .sorry.', re.MULTILINE)


# Lean's identifier continuations include non-word Unicode letter-like characters
# (Init/Meta/Defs.lean). The declaration command itself is sufficient for a hit.
IDENT_REST = r"\w'!?\u03ca-\u03fb\u1f00-\u1ffe\u2100-\u214f\U0001d49c-\U0001d59f"
NAME_PART = r"(?:«[^»\n]+»|[^\s.:«»(){}\[\]]+)"
AXIOM_DECL = re.compile(rf"(?<![{IDENT_REST}.«])axiom(?![{IDENT_REST}»])(?:\s*({NAME_PART}(?:\.{NAME_PART})*))?")
AXIOM_REPORT = re.compile(
    r"^(?:(?:info: )?(?:\./|" + re.escape(str(ROOT)) + r"/)?"
    r"(?P<file>tests/lean/[^:\n]+\.lean):\d+:\d+: (?:info: )?)?"
    r"'(?P<name>[^\n]+?)' depends on axioms:\s*\[(?P<deps>[^\]]*)\]", re.MULTILINE)
STANDARD_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}


def axiom_reports(text, direct_file, accepted):
    for match in AXIOM_REPORT.finditer(text):
        file = match['file'] or direct_file
        if file is None:
            continue
        name = match['name']
        deps = {item.strip() for item in match['deps'].split(',')} - STANDARD_AXIOMS
        if (file, name) in accepted:
            deps.discard('sorryAx')
        for dep in sorted(deps):
            yield f'AXIOM dependency\t{file}\t{name}\t{dep}'


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
# Tactic position only, in code: `admit` and `stop` are also English words and names.
TACTICS = re.compile(r'(?:^|\bby\b|<;>|;|\(|·)\s*admit\b|(?:\bby\b|<;>|;|·)\s*stop\b|^\s*stop\s*$')
# A guard anywhere in code (`open Nat in #guard_msgs ...`), with the docstring before it that holds the
# messages it expects.
GUARD = re.compile(r'(?:/--((?:(?!-/).)*?)-/\s*)?#guard_msgs\b', re.DOTALL)
GUARD_END = re.compile(r'\bin\b')
# Command-level metaprogramming can build a hiding guard or a sorry out of pieces no rule here sees.
META = re.compile(r'(?<![\w.])(macro_rules|macro|syntax|elab_rules|elab|notation|infixl|infixr|infix|prefix|postfix)'
                  r'(?![\w\'!?»])')
META_NAME = re.compile(r'\s*(?:\(\s*name\s*:=\s*([^\s)]+)\s*\)\s*)?(?:\(\s*priority\s*:=[^)]*\)\s*)?'
                       r'(?:"([^"]*)"|([^\s(:"]+))?')


def views(text):
    """The text with comments and string contents blanked (code), and the same keeping docstrings (guards).

    Both keep every offset and newline. Lean block comments nest.
    """
    code, guard = list(text), list(text)

    def blank(buffer, start, end):
        for k in range(start, end):
            if buffer[k] != '\n':
                buffer[k] = ' '
    i, n = 0, len(text)
    while i < n:
        if text.startswith('--', i):
            end = text.find('\n', i)
            end = n if end < 0 else end
            blank(code, i, end)
            blank(guard, i, end)
            i = end
        elif text.startswith('/-', i):
            depth, end = 1, i + 2
            while end < n and depth:
                if text.startswith('/-', end):
                    depth, end = depth + 1, end + 2
                elif text.startswith('-/', end):
                    depth, end = depth - 1, end + 2
                else:
                    end += 1
            blank(code, i, end)
            if not text.startswith('/--', i):
                blank(guard, i, end)
            i = end
        elif text[i] == '"':
            end = i + 1
            while end < n and text[end] != '"':
                end += 2 if text[end] == '\\' else 1
            blank(code, i + 1, end)
            blank(guard, i + 1, end)
            i = end + 1
        elif text.startswith(("'\"'", "'\\\"'"), i):  # the character literals '"' and '\"'
            i += 3 if text.startswith("'\"'", i) else 4
        else:
            i += 1
    return ''.join(code), ''.join(guard)


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


def tripwires(root, accepted, metaprograms=frozenset()):
    """Source lines that use or could hide a `sorry` outside the allowlists."""
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
        code, guards = views(text)
        code_lines = code.splitlines()

        def named(*texts):
            return any(re.search(r'(?<![\w.])' + re.escape(name) + r'(?![\w.])', t) for name in names for t in texts)
        for number, line in enumerate(lines, 1):
            if not named(line):
                hits += [f'{file}:{number}: {match.group(0).strip()}' for match in
                         [*TEST_WORDS.finditer(line), *TACTICS.finditer(code_lines[number - 1])]]
        for match in AXIOM_DECL.finditer(code):
            name = match[1] or '?'
            if match[1] is None or (file, name) not in accepted:
                hits.append(f'{file}:{text.count(chr(10), 0, match.start()) + 1}: axiom {name}')
        for match in META.finditer(code):
            found = META_NAME.match(text, match.end())
            name = match.group(1) if match.group(1) == 'macro_rules' else \
                (found.group(1) or found.group(2) or found.group(3) or '?')
            if (file, name) not in metaprograms:
                hits.append(f'{file}:{text.count(chr(10), 0, match.start()) + 1}: {match.group(1)} {name} '
                            f'(metaprogramming outside {META_ALLOWLIST.name})')
        for match in GUARD.finditer(guards):
            number = text.count('\n', 0, match.end()) + 1
            if named(*lines[number - 1:number + 1]):
                continue
            if match.group(1) and re.search(r'\bwarning\b', match.group(1), re.IGNORECASE):
                hits.append(f'{file}:{number}: #guard_msgs expecting a warning')
            header = text[match.end():match.end() + len(guard_header(guards, match.end()))]
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
    parser.add_argument('--meta-allowlist', type=Path, default=META_ALLOWLIST)
    parser.add_argument('--test-file', help='test file of a direct Lean run (bare #print axioms output)')
    parser.add_argument('--sources', action='store_true', help='check the sources for ways to hide the warning')
    parser.add_argument('--root', type=Path, default=ROOT, help=argparse.SUPPRESS)
    args = parser.parse_args()
    if args.sources:
        hits = tripwires(args.root, allowed(args.allowlist), allowed(args.meta_allowlist))
        if hits:
            raise ValueError('unapproved test source:\n' + '\n'.join(hits))
        print('[ok] test sources passed the proof and metaprogramming checks')
    accepted = allowed(args.allowlist)
    found = set()
    reports = set()
    for log in args.logs:
        text = log.read_text(errors='replace')
        reports.update(axiom_reports(text, args.test_file, accepted))
        for match in WARNING.finditer(text):
            file, line, column = match.group(1), int(match.group(2)), int(match.group(3))
            found.add((file, declaration(file, line, column), f'{file}:{line}:{column}'))
    rejected = sorted(f'SORRY\t{file}\t{name}\t({where})' for file, name, where in found
                      if (file, name) not in accepted)
    if reports:
        rejected.extend(sorted(reports))
    if rejected:
        raise ValueError(f'unapproved test evidence ({args.allowlist.name}):\n' + '\n'.join(rejected))


if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError) as error:
        print(f'[FAIL] {error}', file=sys.stderr)
        raise SystemExit(1)
