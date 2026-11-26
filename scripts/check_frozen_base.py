#!/usr/bin/env python3
"""Check that no row recorded on the main branch changed in the frozen tables.

check_frozen_statements.py compares the two tables only with the build of the
same branch, so a branch that edits a table, or runs --fill or
--accept-definitions, still passes it. This check reads both tables at their
fixed paths documents/dist/FrozenStatements.tsv and FrozenDefinitions.tsv,
once at `git merge-base HEAD <main>` and once in the working tree, and fails
when a row recorded at the merge base was deleted or its fingerprint or its
`signed` text changed. It also fails when a table, or a directory on its path,
is a symbolic link.

A statement whose fingerprint and `signed` text are unchanged may change only
its module to one outside VeriTile.Staging: the move to a main target that
documents/ContributorGuide.md prescribes. It is printed as `[moved]`;
check_frozen_statements.py checks that the new module declares it. New rows
pass here; check_frozen_statements.py accepts them only with `-` or with the
computed fingerprint.

<main> is --main, else fork/main, else origin/main; if none exists, or HEAD
has no merge base with it, the check fails.

Override, for the coordinator's sign-off and re-sign batches only:
VERITILE_FROZEN_OVERRIDE=name,name,... allows exactly the named rows (first
column, either table) to change or disappear, and every named row must differ.
Whenever the variable is set, the check says so and prints each overridden
row. scripts/local_gate.sh unsets it, so the gate always checks without it;
the coordinator runs the override check separately.
"""
import argparse
import os
from pathlib import Path
import subprocess
import sys

from check_frozen_statements import DEFINITION_HEADER, ROOT, STATEMENT_HEADER, read

OVERRIDE = 'VERITILE_FROZEN_OVERRIDE'
STATEMENTS = 'documents/dist/FrozenStatements.tsv'
DEFINITIONS = 'documents/dist/FrozenDefinitions.tsv'


def git(repo, *args):
    return subprocess.run(['git', '-C', str(repo), *args], text=True, capture_output=True)


def rows(relative, header, text):
    return {row[0]: row for row in read(Path(relative), header, text)[1].values()}


def staging(module):
    return module == 'VeriTile.Staging' or module.startswith('VeriTile.Staging.')


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--main', help='main branch ref (default: fork/main, else origin/main)')
    parser.add_argument('--repo', type=Path, default=ROOT, help='repository to check (default: this one)')
    args = parser.parse_args()
    repo = args.repo
    candidates = [args.main] if args.main else ['fork/main', 'origin/main']
    ref = next((r for r in candidates if not git(repo, 'rev-parse', '--verify', '--quiet', r + '^{commit}').returncode),
               None)
    if ref is None:
        raise ValueError(f'no main ref found among {", ".join(candidates)}')
    merged = git(repo, 'merge-base', 'HEAD', ref)
    if merged.returncode:
        raise ValueError(f'no merge base of HEAD and {ref}')
    base = merged.stdout.strip()
    if OVERRIDE in os.environ:
        print(f'[override] {OVERRIDE} is set: {os.environ[OVERRIDE]!r}')
    allowed = {name.strip() for name in os.environ.get(OVERRIDE, '').split(',') if name.strip()}
    changed, errors, overridden, moved, counts = set(), [], [], [], []
    for relative, header, key in ((STATEMENTS, STATEMENT_HEADER, slice(1, 4)), (DEFINITIONS, DEFINITION_HEADER, slice(1, 2))):
        parts = relative.split('/')
        links = [p for p in ('/'.join(parts[:i]) for i in range(1, len(parts) + 1)) if (repo / p).is_symlink()]
        if links:
            raise ValueError(f'{links[0]} is a symbolic link; the frozen tables must be regular files at {relative}')
        # A table absent at the merge base has no recorded rows; one absent now has none left.
        shown = git(repo, 'show', f'{base}:{relative}') \
            if not git(repo, 'cat-file', '-e', f'{base}:{relative}').returncode else None
        if shown and shown.returncode:
            raise ValueError(f'cannot read {relative} at {base}')
        old = rows(relative, header, shown.stdout if shown else '')
        path = repo / relative
        new = rows(relative, header, path.read_text() if path.exists() else '')
        table = parts[-1]
        counts.append(f'{len(old)} {table} row(s), {len(set(new) - set(old))} new')
        for name, row in old.items():
            now = new.get(name)
            if now and now[key] == row[key]:
                continue
            if now and key.stop == 4 and now[2:4] == row[2:4] and not staging(now[1]):
                moved.append(f'{name}: {row[1]} → {now[1]}')
                continue
            line = f'{table}: {name}: recorded {" ".join(row[key])}, now ' + (' '.join(now[key]) if now else 'deleted')
            changed.add(name)
            (overridden if name in allowed else errors).append(line)
    for name in sorted(allowed - changed):
        errors.append(f'{OVERRIDE} names {name}, which did not change')
    for line in moved:
        print(f'[moved] {line}')
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
