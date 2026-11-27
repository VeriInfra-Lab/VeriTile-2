#!/usr/bin/env python3
"""Fail on a staging import in bench/ other than the TritonDistProgram bridge.

Decision Q1 (a) on #82 lets the bench/ K transcriptions import exactly one
staging module, ALLOWED below, until #48 moves it to a main target (#704).
Main targets stay barred from every staging import by check_fork_target.py.

The check scans every tracked .lean file under bench/ (`git ls-files`) and
fails if it finds none. Comments and string contents are blanked first
(check_test_sorry.views). The module after `import` (or `import all`) is split
into name components with check_test_sorry.LEX_PART, each a plain identifier
or one `«…»` atom, and `«»` is removed per component. The module is staging if
its first two components are `VeriTile`, `Staging`; it must then have exactly
the components of ALLOWED. So `VeriTile.Staging.«Dist.TritonDistProgram»` and
`VeriTile.Staging.Dist.«TritonDistProgram X»` fail: they are other files.
Path-like components (`VeriTile.«Staging/X»`, `bench.«..».VeriTile.Staging.X`)
are rejected in every tracked Lean file by check_import_paths.py, whose import
parsing this check shares.

The check is textual and reads direct imports only. Known blind spots:
- staging reached transitively: e.g. a bench/ file importing a tests/lean/dist
  module that imports staging is not caught;
- an import whose module name is built by a macro.
"""
from pathlib import Path
import sys

from check_import_paths import imports, lean_files

ROOT = Path(__file__).resolve().parents[1]
# The only staging module bench/ may import; remove this check once #48 moves it to a main target (#704).
ALLOWED = 'VeriTile.Staging.Dist.TritonDistProgram'
ALLOWED_PARTS = tuple(ALLOWED.split('.'))


def check(root):
    """Return (number of bench/ Lean files scanned, violations as `path:line: module`)."""
    files = lean_files(root, 'bench')
    hits = [f'{path}:{line}: {module}' for path, line, module, name in imports(root, files)
            if name[:2] == ALLOWED_PARTS[:2] and name != ALLOWED_PARTS]
    return len(files), hits


def main(root=ROOT):
    scanned, hits = check(root)
    for hit in hits:
        print(hit, file=sys.stderr)
    if not scanned:
        print('No tracked bench/ Lean file found; the bench staging-import check scanned nothing.',
              file=sys.stderr)
        return 1
    if hits:
        print(f'{len(hits)} staging import(s) under bench/ other than {ALLOWED} '
              '(decision Q1 (a) on #82, until #48).', file=sys.stderr)
        return 1
    print(f'{scanned} bench/ Lean file(s) import no staging module other than {ALLOWED}.')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
