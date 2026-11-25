#!/usr/bin/env python3
"""Negative examples for the fork target gates.

Writes throwaway probe modules into VeriTile/Dist, VeriTile/Staging and tests/lean, and
removes them again; do not run it while another build uses this checkout.
"""
import hashlib
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
SORRY = 'theorem veritileGateProbe (n : Nat) : n + 0 = n := sorry\n'


def run(script, *args, env=None):
    return subprocess.run([sys.executable, str(ROOT / 'scripts' / script), *args],
                          cwd=ROOT, text=True, capture_output=True, env=env)


class ForkTargetGates(unittest.TestCase):
    def probe(self, relative, text):
        path = ROOT / relative
        self.assertFalse(path.exists(), f'{relative} already exists')
        self.addCleanup(path.unlink)
        path.write_text(text)
        return path

    def test_sorry_fails_a_main_target_and_not_staging(self):
        # The DSL reserves bare `true`; the generated audit must still elaborate.
        self.probe('VeriTile/Dist/GateProbe.lean', 'import VeriTile.Triton.DSL.Syntax\n' + SORRY)
        rejected = run('check_fork_target.py', 'VeriTileDist')
        self.assertNotEqual(rejected.returncode, 0, rejected.stdout)
        self.assertIn('SORRY\tVeriTile.Dist.GateProbe\tveritileGateProbe', rejected.stderr)
        self.probe('VeriTile/Staging/GateProbe.lean', SORRY.replace('Probe', 'StagingProbe'))
        accepted = run('check_fork_target.py', 'VeriTileStaging')
        self.assertEqual(accepted.returncode, 0, accepted.stderr)

    def test_main_target_cannot_import_staging(self):
        self.probe('VeriTile/Staging/GateProbe.lean', 'def veritileGateStagingProbe := 0\n')
        self.probe('VeriTile/Dist/GateProbe.lean', 'import VeriTile.Staging.GateProbe\n')
        rejected = run('check_fork_target.py', 'VeriTileDist')
        self.assertNotEqual(rejected.returncode, 0, rejected.stdout)
        self.assertIn('STAGING\tVeriTile.Staging.GateProbe', rejected.stderr)

    def test_main_target_cannot_declare_an_axiom(self):
        self.probe('VeriTile/Dist/GateProbe.lean', 'axiom veritileGateProbe : 0 = 0\n')
        rejected = run('check_fork_target.py', 'VeriTileDist')
        self.assertNotEqual(rejected.returncode, 0, rejected.stdout)
        self.assertIn('AXIOM\tVeriTile/Dist/GateProbe.lean:veritileGateProbe', rejected.stderr)

    def test_sorry_in_a_test_file_fails(self):
        relative = 'tests/lean/GateSorryProbe.lean'
        self.probe(relative, 'theorem veritileTestSorryProbe : True := sorry\nexample : True := sorry\n')
        # The gate runs `lake env lean tests/lean/...` and scans its output; Lake's replayed form must match too.
        ran = subprocess.run(['lake', 'env', 'lean', relative], cwd=ROOT, text=True, capture_output=True)
        self.assertEqual(ran.returncode, 0, ran.stdout + ran.stderr)
        with tempfile.TemporaryDirectory() as temp:
            log, allowlist = Path(temp) / 'command.log', Path(temp) / 'allowlist.txt'
            log.write_text(ran.stdout + ran.stderr +
                           f'warning: {relative}:1:8: declaration uses `sorry`\n'
                           'warning: VeriTile/Staging/Probe.lean:1:8: declaration uses `sorry`\n')
            allowlist.write_text(f'{relative}\texample\tprobe\n')
            rejected = run('check_test_sorry.py', str(log), '--allowlist', str(allowlist))
            self.assertNotEqual(rejected.returncode, 0, rejected.stdout)
            self.assertIn(f'SORRY\t{relative}\tveritileTestSorryProbe\t({relative}:1:8)', rejected.stderr)
            self.assertNotIn('\texample\t', rejected.stderr)
            self.assertNotIn('Staging', rejected.stderr)
            allowlist.write_text(f'{relative}\texample\tprobe\n{relative}\tveritileTestSorryProbe\tprobe\n')
            accepted = run('check_test_sorry.py', str(log), '--allowlist', str(allowlist))
            self.assertEqual(accepted.returncode, 0, accepted.stderr)
            allowlist.write_text(f'{relative}\tveritileTestSorryProbe\tprobe\n')
            rejected = run('check_test_sorry.py', str(log), '--allowlist', str(allowlist))
            self.assertIn(f'SORRY\t{relative}\texample\t({relative}:2:0)', rejected.stderr)

    def test_frozen_statement_rejects_an_importing_module(self):
        owner = 'VeriTile.Staging.FrozenOwnerProbe'
        importer = 'VeriTile.Staging.FrozenImportProbe'
        name = 'frozenOwnerProbe'
        self.probe('VeriTile/Staging/FrozenOwnerProbe.lean', f'theorem {name} : True := True.intro\n')
        self.probe('VeriTile/Staging/FrozenImportProbe.lean', f'import {owner}\n')
        # The elaborated type is the constant True with no universe levels or project dependencies.
        digest = hashlib.sha256(b'(C True [])').hexdigest()
        with tempfile.TemporaryDirectory() as temp:
            tsv = Path(temp) / 'Statements.tsv'
            args = ['--tsv', str(tsv), '--definitions', str(Path(temp) / 'Definitions.tsv')]

            def record(module):
                tsv.write_text(f'statement\tmodule\tsha256\tsigned\n{name}\t{module}\t{digest}\ttest\n')

            record(owner)
            accepted = run('check_frozen_statements.py', *args)
            self.assertEqual(accepted.returncode, 0, accepted.stderr)
            record(importer)
            rejected = run('check_frozen_statements.py', *args)
            self.assertNotEqual(rejected.returncode, 0, rejected.stdout)
            self.assertIn(f'{tsv.name}:2: {name}: recorded module {importer}, declared in {owner}', rejected.stderr)

    def test_frozen_statement_and_its_definitions(self):
        source = ('namespace VeriTileGateProbe\n'
                  'def limit : Nat := 4\n'
                  'def stub : Nat := sorry\n'
                  'def Small (n : Nat) : Prop := n < limit ∨ n < stub\n'
                  'theorem bound (n : Nat) : Small n → n < 10 := sorry\n'
                  'end VeriTileGateProbe\n')
        probe = self.probe('VeriTile/Staging/GateProbe.lean', source)
        with tempfile.TemporaryDirectory() as temp:
            tsv, definitions = Path(temp) / 'FrozenStatements.tsv', Path(temp) / 'FrozenDefinitions.tsv'
            tsv.write_text('statement\tmodule\tsha256\tsigned\n'
                           'VeriTileGateProbe.bound\tVeriTile.Staging.GateProbe\t-\ttest\n')

            def check(*flags):
                return run('check_frozen_statements.py', '--tsv', str(tsv), '--definitions', str(definitions), *flags)
            self.assertNotEqual(check().returncode, 0)  # nothing recorded yet
            self.assertEqual(check('--fill').returncode, 0)
            self.assertEqual(sorted(line.split('\t')[0] for line in definitions.read_text().splitlines()[1:]),
                             ['VeriTileGateProbe.Small', 'VeriTileGateProbe.limit', 'VeriTileGateProbe.stub'])
            # Moving a stub to another line changes the position tag of its `sorry`, not its fingerprint.
            probe.write_text('\n\n' + source)
            moved = check()
            self.assertEqual(moved.returncode, 0, moved.stderr)
            # Renaming a bound variable or rewriting the proof changes neither fingerprint.
            probe.write_text(source.replace('(n : Nat) : Small n → n < 10 := sorry',
                                            '(m : Nat) : Small m → m < 10 := sorry'))
            same = check()
            self.assertEqual(same.returncode, 0, same.stderr)
            probe.write_text(source.replace('n < 10', 'n < 11'))
            edited = check()
            self.assertNotEqual(edited.returncode, 0, edited.stdout)
            self.assertIn('VeriTileGateProbe.bound: statement changed since sign-off', edited.stderr)
            # A definition used only inside another definition's body still changes the meaning.
            probe.write_text(source.replace('limit : Nat := 4', 'limit : Nat := 400'))
            redefined = check()
            self.assertNotEqual(redefined.returncode, 0, redefined.stdout)
            self.assertIn('VeriTileGateProbe.limit: definition changed since it was recorded; '
                          'affects VeriTileGateProbe.bound', redefined.stderr)
            self.assertNotIn('statement changed', redefined.stderr)
            self.assertNotEqual(check('--fill').returncode, 0)  # --fill never replaces a fingerprint
            before = definitions.read_text().splitlines()
            self.assertEqual(check('--accept-definitions').returncode, 0)
            after = definitions.read_text().splitlines()
            self.assertEqual([a == b for a, b in zip(before, after)], [True, True, False, True])
            self.assertEqual(check().returncode, 0)
            # A statement re-signed together with a definition it rests on: neither flag alone can do it.
            probe.write_text(source.replace('limit : Nat := 4', 'limit : Nat := 5').replace('n < 10', 'n < 12'))
            tsv.write_text(tsv.read_text().replace(tsv.read_text().splitlines()[1].split('\t')[2], '-'))
            self.assertNotEqual(check('--fill').returncode, 0)
            self.assertNotEqual(check('--accept-definitions').returncode, 0)
            self.assertEqual(check('--fill', '--accept-definitions').returncode, 0)
            self.assertEqual(check().returncode, 0)


class FrozenTablesAgainstBase(unittest.TestCase):
    """check_frozen_base.py on a throwaway repository whose `main` holds the recorded tables."""
    STATEMENTS = ('statement\tmodule\tsha256\tsigned\n'
                  f'P.kept\tM.kept\t{"a" * 64}\tbase\nP.other\tM.other\t{"b" * 64}\tbase\n')
    DEFINITIONS = f'definition\tsha256\nP.Def\t{"d" * 64}\n'

    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.repo = Path(temp.name)
        self.tsv, self.definitions = self.repo / 'Statements.tsv', self.repo / 'Definitions.tsv'
        self.tsv.write_text(self.STATEMENTS)
        self.definitions.write_text(self.DEFINITIONS)
        for command in (['init', '-q', '-b', 'main'], ['add', '.'],
                        ['-c', 'user.name=gate', '-c', 'user.email=gate@example.invalid',
                         '-c', 'commit.gpgsign=false', 'commit', '-qm', 'base']):
            subprocess.run(['git', *command], cwd=self.repo, check=True, capture_output=True)

    def check(self, override=None):
        env = {k: v for k, v in os.environ.items() if k != 'VERITILE_FROZEN_OVERRIDE'}
        if override is not None:
            env['VERITILE_FROZEN_OVERRIDE'] = override
        return run('check_frozen_base.py', '--main', 'main', '--tsv', str(self.tsv),
                   '--definitions', str(self.definitions), env=env)

    def test_deleted_row_fails(self):
        self.tsv.write_text(self.STATEMENTS.replace(self.STATEMENTS.splitlines()[2] + '\n', ''))
        rejected = self.check()
        self.assertNotEqual(rejected.returncode, 0, rejected.stdout)
        self.assertIn('Statements.tsv: P.other: recorded M.other ' + 'b' * 64 + ', now deleted', rejected.stderr)

    def test_changed_fingerprint_fails(self):
        self.tsv.write_text(self.STATEMENTS.replace('a' * 64, 'c' * 64))
        rejected = self.check()
        self.assertNotEqual(rejected.returncode, 0, rejected.stdout)
        self.assertIn(f'P.kept: recorded M.kept {"a" * 64}, now M.kept {"c" * 64}', rejected.stderr)
        # What --accept-definitions would do to a recorded definition.
        self.tsv.write_text(self.STATEMENTS)
        self.definitions.write_text(self.DEFINITIONS.replace('d' * 64, 'e' * 64))
        rejected = self.check()
        self.assertNotEqual(rejected.returncode, 0, rejected.stdout)
        self.assertIn(f'Definitions.tsv: P.Def: recorded {"d" * 64}, now {"e" * 64}', rejected.stderr)

    def test_changed_module_fails(self):
        self.tsv.write_text(self.STATEMENTS.replace('M.kept', 'M.moved'))
        rejected = self.check()
        self.assertNotEqual(rejected.returncode, 0, rejected.stdout)
        self.assertIn(f'P.kept: recorded M.kept {"a" * 64}, now M.moved {"a" * 64}', rejected.stderr)

    def test_added_unfilled_row_passes(self):
        self.tsv.write_text(self.STATEMENTS + 'P.new\tM.new\t-\tnew\n')
        accepted = self.check()
        self.assertEqual(accepted.returncode, 0, accepted.stderr)
        self.assertIn('(2 Statements.tsv row(s), 1 new; 1 Definitions.tsv row(s), 0 new)', accepted.stdout)

    def test_override_allows_exactly_the_named_rows(self):
        self.tsv.write_text(self.STATEMENTS.replace('a' * 64, 'c' * 64))
        self.definitions.write_text(self.DEFINITIONS.replace('d' * 64, 'e' * 64))
        self.assertNotEqual(self.check().returncode, 0)
        self.assertNotEqual(self.check('P.kept').returncode, 0)  # P.Def is still not named
        self.assertNotEqual(self.check('P.kept,P.Def,P.other').returncode, 0)  # P.other did not change
        accepted = self.check('P.kept, P.Def')
        self.assertEqual(accepted.returncode, 0, accepted.stderr)
        self.assertIn('[override] Statements.tsv: P.kept: recorded', accepted.stdout)
        self.assertIn('[override] Definitions.tsv: P.Def: recorded', accepted.stdout)


if __name__ == '__main__':
    unittest.main()
