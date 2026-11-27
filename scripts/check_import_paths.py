#!/usr/bin/env python3
"""Fail on an import whose module name has a path-like component, in any tracked Lean file.

Lean finds a module's file by joining its name components with `/`. A quoted
component that is empty, `.` or `..`, or contains `/` or `\\`, can therefore
name a file that the name does not spell, e.g. `VeriTile.«Staging/X»` or
`bench.«..».VeriTile.Staging.X` reach VeriTile/Staging/X.lean. Such names
bypass the staging rules of check_bench_staging_imports.py and
check_fork_target.py, and no real module needs one (#704, re-review of #706).

The check scans every tracked .lean file (`git ls-files`) and fails if it
finds none. Comments and string contents are blanked first
(check_test_sorry.views). The module after `import` (or `import all`) is split
into components with check_test_sorry.LEX_PART, each a plain identifier or one
`«…»` atom, and `«»` is removed per component. A dot inside one `«…»` atom is
not a path separator: `«VeriTile.Staging».X` is the file VeriTile.Staging/X.lean.
"""
from pathlib import Path
import re
import subprocess
import sys

from check_test_sorry import LEX_PART, views

ROOT = Path(__file__).resolve().parents[1]
IMPORT = re.compile(rf"(?<![\w'!?.])import\s+(?:all\s+)?({LEX_PART}(?:\.{LEX_PART})*)")


def parts(module):
    """The name components of `module`, each with its `«»` removed."""
    return tuple(p[1:-1] if p.startswith('«') and p.endswith('»') else p
                 for p in re.findall(LEX_PART, module))


def path_like(component):
    return component in ('', '.', '..') or '/' in component or '\\' in component


def imports(root, files):
    """Yield (path, line, module as written, components) for every import in `files`."""
    for relative in files:
        code, _ = views((root / relative).read_text())
        for match in IMPORT.finditer(code):
            yield relative, code.count('\n', 0, match.start()) + 1, match[1], parts(match[1])


def lean_files(root, *pathspec):
    """Tracked .lean files; a plain or empty pathspec, filtered here, ignores GIT_*_PATHSPECS."""
    listed = subprocess.run(['git', 'ls-files', '-z', '--', *pathspec], cwd=root,
                            capture_output=True, text=True, check=True).stdout
    return [f for f in sorted(filter(None, listed.split('\0')))
            if f.endswith('.lean') and (root / f).is_file()]


def check(root):
    """Return (number of Lean files scanned, violations as `path:line: module`)."""
    files = lean_files(root)
    hits = [f'{path}:{line}: {module}' for path, line, module, name in imports(root, files)
            if any(map(path_like, name))]
    return len(files), hits


def main(root=ROOT):
    scanned, hits = check(root)
    for hit in hits:
        print(hit, file=sys.stderr)
    if not scanned:
        print('No tracked Lean file found; the import-path check scanned nothing.', file=sys.stderr)
        return 1
    if hits:
        print(f'{len(hits)} import(s) with a path-like name component (empty, `.`, `..`, `/` or `\\`); '
              'Lean would read a file the name does not spell.', file=sys.stderr)
        return 1
    print(f'{scanned} tracked Lean file(s) import no module with a path-like name component.')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
