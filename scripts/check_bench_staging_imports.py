#!/usr/bin/env python3
"""Fail on a staging import in bench/ other than the TritonDistProgram bridge.

Decision Q1 (a) on #82 lets the bench/ K transcriptions import exactly one
staging module, ALLOWED below, until #48 moves it to a main target (#704).
Main targets stay barred from every staging import by check_fork_target.py.

The check scans every tracked .lean file under bench/ (`git ls-files`).
Comments and string contents are blanked first (check_test_sorry.views). The
module after `import` (or `import all`) is compared with `«»` removed: it is
staging if it is `VeriTile.Staging` or below it, and must then equal ALLOWED.

The check is textual. Known blind spots:
- a staging module reached transitively through a non-staging import;
- an import whose module name is split across lines or built by a macro.
"""
from pathlib import Path
import re
import subprocess
import sys

from check_test_sorry import views

ROOT = Path(__file__).resolve().parents[1]
# The only staging module bench/ may import; remove this check once #48 moves it to a main target (#704).
ALLOWED = 'VeriTile.Staging.Dist.TritonDistProgram'
STAGING = 'VeriTile.Staging'
IMPORT = re.compile(r"(?<![\w'!?.])import\s+(?:all\s+)?(\S+)")


def check(root):
    listed = subprocess.run(['git', 'ls-files', '-z', '--', 'bench/*.lean'], cwd=root,
                            capture_output=True, text=True, check=True).stdout
    hits = []
    for relative in sorted(filter(None, listed.split('\0'))):
        path = root / relative
        if not path.is_file():
            continue
        code, _ = views(path.read_text())
        for match in IMPORT.finditer(code):
            module = match[1].replace('«', '').replace('»', '')
            if (module == STAGING or module.startswith(STAGING + '.')) and module != ALLOWED:
                hits.append(f'{relative}:{code.count(chr(10), 0, match.start()) + 1}: {module}')
    return hits


def main(root=ROOT):
    hits = check(root)
    for hit in hits:
        print(hit, file=sys.stderr)
    if hits:
        print(f'{len(hits)} staging import(s) under bench/ other than {ALLOWED} '
              '(decision Q1 (a) on #82, until #48).', file=sys.stderr)
        return 1
    print(f'bench/ imports no staging module other than {ALLOWED}.')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
