#!/usr/bin/env python3
"""Check that no row recorded on the main branch changed in the frozen tables.

check_frozen_statements.py compares the two tables only with the build of the
same branch, so a branch that edits a table, or runs --fill or
--accept-definitions, still passes it. This check reads both tables at
`git merge-base HEAD <main>` and in the working tree. It fails when a row
recorded at the merge base was deleted, or its fingerprint or (for a
statement) its module changed. New rows pass here; check_frozen_statements.py
accepts them only with `-` or with the computed fingerprint.

<main> is --main, else the first of fork/main, origin/main and main that exists.

Override, for the coordinator's sign-off and re-sign batches only:
VERITILE_FROZEN_OVERRIDE=name,name,... allows exactly the named rows (first
column, either table) to change or disappear, and every named row must differ.
scripts/local_gate.sh never sets it; each overridden row is printed.
"""
import argparse
import os
from pathlib import Path
import subprocess
import sys

from check_frozen_statements import DEFINITION_HEADER, DEFINITIONS, STATEMENT_HEADER, STATEMENTS, read

OVERRIDE = 'VERITILE_FROZEN_OVERRIDE'


def git(repo, *args):
    return subprocess.run(['git', '-C', str(repo), *args], text=True, capture_output=True)


def rows(path, header, text=None):
    return {row[0]: row for row in read(path, header, text)[1].values()}


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--main', help='main branch ref (default: fork/main, origin/main or main)')
    parser.add_argument('--tsv', type=Path, default=STATEMENTS)
    parser.add_argument('--definitions', type=Path, default=DEFINITIONS)
    args = parser.parse_args()
    top = git(args.tsv.resolve().parent, 'rev-parse', '--show-toplevel')
    if top.returncode:
        raise ValueError(f'{args.tsv} is not in a Git repository')
    repo = Path(top.stdout.strip()).resolve()
    candidates = [args.main] if args.main else ['fork/main', 'origin/main', 'main']
    ref = next((r for r in candidates if not git(repo, 'rev-parse', '--verify', '--quiet', r + '^{commit}').returncode),
               None)
    if ref is None:
        raise ValueError(f'no main ref found among {", ".join(candidates)}')
    merged = git(repo, 'merge-base', 'HEAD', ref)
    if merged.returncode:
        raise ValueError(f'no merge base of HEAD and {ref}')
    base = merged.stdout.strip()
    allowed = {name.strip() for name in os.environ.get(OVERRIDE, '').split(',') if name.strip()}
    changed, errors, overridden, counts = set(), [], [], []
    for path, header, key in ((args.tsv, STATEMENT_HEADER, slice(1, 3)), (args.definitions, DEFINITION_HEADER, slice(1, 2))):
        relative = path.resolve().relative_to(repo).as_posix()
        # A table absent at the merge base has no recorded rows.
        shown = git(repo, 'show', f'{base}:{relative}') \
            if not git(repo, 'cat-file', '-e', f'{base}:{relative}').returncode else None
        if shown and shown.returncode:
            raise ValueError(f'cannot read {relative} at {base}')
        old = rows(path, header, shown.stdout) if shown else {}
        new = rows(path, header)
        counts.append(f'{len(old)} {path.name} row(s), {len(set(new) - set(old))} new')
        for name, row in old.items():
            if name in new and new[name][key] == row[key]:
                continue
            now = ' '.join(new[name][key]) if name in new else 'deleted'
            line = f'{path.name}: {name}: recorded {" ".join(row[key])}, now {now}'
            changed.add(name)
            (overridden if name in allowed else errors).append(line)
    for name in sorted(allowed - changed):
        errors.append(f'{OVERRIDE} names {name}, which did not change')
    for line in overridden:
        print(f'[override] {line}')
    if errors:
        raise ValueError(f'frozen rows recorded at the merge base {base[:12]} with {ref} changed:\n' +
                         '\n'.join(errors) + f'\nOnly a coordinator sign-off may change them, by naming the rows in '
                         f'{OVERRIDE} (see --help).')
    print(f'[ok] frozen tables keep every row of the merge base {base[:12]} with {ref} ({"; ".join(counts)})')


if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError) as error:
        print(f'[FAIL] {error}', file=sys.stderr)
        raise SystemExit(1)
