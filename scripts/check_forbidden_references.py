#!/usr/bin/env python3
"""Fail on a reference to the unrestated C3 outside VeriTile/Staging/Dist/JudgmentSpec.lean.

User decision of 2026-11-26: until C3 is restated, no file outside
JudgmentSpec.lean may reference the known-false C3 statement or the theorem
derived from it, so that no kernel proof is built on a false statement.

Remove this check when C3 is restated under the E2 decision (#53/#54) and
re-signed.

The check scans every .lean file under VeriTile/ and tests/ except that one
file. Comments (`--`, nested `/- -/`, docstrings) and string contents are
blanked first (check_test_sorry.views). A name matches as a whole Lean
identifier: also qualified (`VeriTile.Dist.NAME`), in `open ... (NAME)`, as
`«NAME»` or a name literal, and followed by `.field`; not with an extra
prefix or suffix (`my_NAME`, `NAME'`, `NAME₁`). A declaration of the same
name in another namespace is flagged on purpose.

The check is textual. It does not see a use through an alias declared inside
JudgmentSpec.lean, a use by automation that does not name the theorem, or a
name inside `s!"{...}"` interpolation (string contents are blanked).
"""
from pathlib import Path
import re
import sys

from check_test_sorry import views

ROOT = Path(__file__).resolve().parents[1]
EXEMPT = 'VeriTile/Staging/Dist/JudgmentSpec.lean'
DIRECTORIES = ('VeriTile', 'tests')
NAMES = ('detRaceFree_scopeConsistent_complete_eq_canonical',  # C3 on main
         'detRaceFree_complete_eq_canonical',  # C3 as PR #615 renames it
         'implementsAll_of_canonical')  # derived from C3
# Lean identifier characters around the name: letters, digits (subscripts too), `_`, `'`, `!`, `?`.
PATTERN = re.compile(r"(?<![\w'!?])(" + '|'.join(NAMES) + r")(?![\w'!?])")
REMOVAL = 'Remove this check when C3 is restated under the E2 decision (#53/#54) and re-signed.'


def check(root):
    hits = []
    for directory in DIRECTORIES:
        for path in sorted((root / directory).rglob('*.lean')):
            relative = path.relative_to(root).as_posix()
            if relative == EXEMPT:
                continue
            code, _ = views(path.read_text())
            for match in PATTERN.finditer(code):
                hits.append(f'{relative}:{code.count(chr(10), 0, match.start()) + 1}: {match[1]}')
    return hits


def main(root=ROOT):
    hits = check(root)
    for hit in hits:
        print(hit, file=sys.stderr)
    if hits:
        print(f'{len(hits)} reference(s) to the unrestated C3 outside {EXEMPT}. '
              f'Until C3 is restated, no proof may use it. {REMOVAL}', file=sys.stderr)
        return 1
    print(f'No reference to the unrestated C3 outside {EXEMPT}. {REMOVAL}')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
