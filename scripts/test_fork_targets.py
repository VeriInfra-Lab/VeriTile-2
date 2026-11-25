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
                           'warning: VeriTile/Staging/Probe.lean:1:8: declaration uses `sorry`\n'
                           # A dependency's own tests/lean is not this repository's.
                           'warning: .lake/packages/dep/tests/lean/Dep.lean:1:8: declaration uses `sorry`\n')
            allowlist.write_text(f'{relative}\texample\tprobe\n')
            rejected = run('check_test_sorry.py', str(log), '--allowlist', str(allowlist))
            self.assertNotEqual(rejected.returncode, 0, rejected.stdout)
            self.assertIn(f'SORRY\t{relative}\tveritileTestSorryProbe\t({relative}:1:8)', rejected.stderr)
            self.assertNotIn('\texample\t', rejected.stderr)
            self.assertNotIn('Staging', rejected.stderr)
            self.assertNotIn('Dep.lean', rejected.stderr)
            allowlist.write_text(f'{relative}\texample\tprobe\n{relative}\tveritileTestSorryProbe\tprobe\n')
            accepted = run('check_test_sorry.py', str(log), '--allowlist', str(allowlist))
            self.assertEqual(accepted.returncode, 0, accepted.stderr)
            allowlist.write_text(f'{relative}\tveritileTestSorryProbe\tprobe\n')
            rejected = run('check_test_sorry.py', str(log), '--allowlist', str(allowlist))
            self.assertIn(f'SORRY\t{relative}\texample\t({relative}:2:0)', rejected.stderr)

    def test_sources_that_hide_sorry_warnings_fail(self):
        # Each of these silenced the warning in a real build or `lake env lean` run (PR #605 reviews).
        # A body without any sorry source, so that each case depends only on its own rule.
        quiet = 'example : True := trivial\n'
        hiding = {
            'lakefile.toml': '[[lean_lib]]\nname = "FinalRegressions"\nleanOptions = { warn.sorry = false }\n',
            'library/lakefile.toml': 'moreLeanArgs = ["-Dwarn.sorry=false"]\n',
            'tests/lean/Quiet.lean': 'set_option warn.sorry false in\ntheorem t : 1 = 2 := sorry\n',
            'tests/lean/Guarded.lean': '/-- warning: declaration uses `sorry` -/\n#guard_msgs in\n' + quiet,
            # Round 3: one-token variants of the same hides.
            'tests/lean/DropWarning.lean': '#guard_msgs (drop warning) in\n' + quiet,
            'tests/lean/DropAll.lean': '#guard_msgs (drop all) in\n' + quiet,
            'tests/lean/QuotedOption.lean': 'set_option warn.«sorry» false in\n' + quiet,
            'tests/lean/LaxGuard.lean': ('/-- warning: declaration\nuses `sorry` -/\n'
                                         '#guard_msgs (whitespace := lax) in\n' + quiet),
            'tests/lean/SorryAx.lean': 'example : 1 = 2 := sorryAx _ false\n',
            'nested lakefile': '[[lean_lib]]\nname = "FinalRegressions"\nleanOptions = { warn = { sorry = false } }\n',
            # Round 4: a substring guard swallows the warning of an `admit` or `stop`.
            'tests/lean/SubstringWarning.lean': '/-- warning -/\n#guard_msgs (substring := true) in\n'
                                                'theorem t : 1 = 2 := by admit\n',
            # These two guards pass the substring rule, so only the warning-docstring rule catches them.
            'tests/lean/MultiLineWarning.lean': '/-- info: ok\n---\nWarning: declaration\n-/\n'
                                                '#guard_msgs (whitespace := lax) in\nexample : True := trivial\n',
            'tests/lean/SubstringGuard.lean': '/-- warning: declaration uses -/\n#guard_msgs (error, substring := true) in\n'
                                              'example : True := trivial\n',
            'tests/lean/ThenAdmit.lean': 'theorem t : 1 = 2 ∧ 1 = 2 := by constructor <;> admit\n',
            'tests/lean/BulletAdmit.lean': 'theorem t : 1 = 2 := by\n  · admit\n',
            'tests/lean/LineAdmit.lean': 'theorem t : 1 = 2 := by\n  admit\n',
            'tests/lean/Stop.lean': 'theorem t : 1 = 2 := by stop\n  simp\n',
            'tests/lean/LineStop.lean': 'theorem t : 1 = 2 := by\n  stop\n  simp\n',
            # Round 5: a substring guard that captures warnings, whatever produces the sorry.
            'tests/lean/AllGoals.lean': '#guard_msgs (substring := true) in\ntheorem t : 1 = 2 := by all_goals admit\n',
            'tests/lean/Try.lean': '#guard_msgs (substring := true) in\ntheorem t : 1 = 2 := by try admit\n',
            'tests/lean/First.lean': '#guard_msgs (substring := true) in\ntheorem t : 1 = 2 := by first | admit\n',
            'tests/lean/Case.lean': ('#guard_msgs (substring := true) in\ntheorem t : 1 = 2 ∧ 1 = 2 := by\n'
                                     '  constructor\n  case left => admit\n  case right => admit\n'),
            'tests/lean/Macro.lean': ('macro "trust" : tactic => `(tactic| admit)\n'
                                      '#guard_msgs (substring := true) in\ntheorem t : 1 = 2 := by trust\n'),
            'tests/lean/Compact.lean': '#guard_msgs(substring:=true) in\n' + quiet,
            'tests/lean/Split.lean': '#guard_msgs\n  (substring\n   := true) in\n' + quiet,
            'tests/lean/WarningSeverity.lean': '#guard_msgs (warning, substring := true) in\n' + quiet,
            'tests/lean/AllSeverity.lean': '#guard_msgs (all, substring := true) in\n' + quiet,
            'tests/lean/ErrorAndWarning.lean': '#guard_msgs (error, warning, substring := true) in\n' + quiet,
            # Round 6: Lean reads a comment in the guard header as whitespace.
            'tests/lean/BlockBefore.lean': '#guard_msgs /- x -/ (substring := true) in\n' + quiet,
            'tests/lean/LineBefore.lean': '#guard_msgs -- x\n  (substring := true) in\n' + quiet,
            'tests/lean/BlockInside.lean': '#guard_msgs (/- ) -/ substring := true) in\n' + quiet,
            'tests/lean/LineInside.lean': '#guard_msgs (substring := true -- x\n  ) in\n' + quiet,
            # Round 7: a guard that does not start its line, and command-level metaprogramming.
            'tests/lean/OpenIn.lean': 'open Nat in #guard_msgs (substring := true) in\n' + quiet,
            'tests/lean/GuardMacro.lean': ('macro "q " c:command : command => `(#guard_msgs (substring := true) in $c)\n'
                                           'q ' + quiet),
            'tests/lean/StringDashes.lean': '#eval "--" #guard_msgs (substring := true) in\n' + quiet,
            'tests/lean/NestedComment.lean': '/- a /- b -/ c -/ #guard_msgs (substring := true) in\n' + quiet,
            'tests/lean/PlainMacro.lean': 'macro "triv" : tactic => `(tactic| trivial)\n',
            'tests/lean/Elab.lean': 'open Lean Elab Command in\nelab "go" : command => pure ()\n',
            'tests/lean/Notation.lean': 'local notation "zero" => (0 : Nat)\n',
            'tests/lean/Infix.lean': 'infixl:65 " +++ " => Nat.add\n',
            # A '"' character literal does not open a string that would hide the guard after it.
            'tests/lean/CharQuote.lean': 'def c := \'"\'\n#guard_msgs (substring := true) in\n' + quiet,
        }
        for case, text in hiding.items():
            relative = 'lakefile.toml' if case == 'nested lakefile' else case
            with tempfile.TemporaryDirectory() as temp:
                root = Path(temp)
                (root / 'tests/lean').mkdir(parents=True)
                # Names, English and other guards that must stay allowed.
                (root / 'tests/lean/Clean.lean').write_text(
                    'theorem t : True := trivial  -- admit nothing; stop here\n'
                    'theorem admit (stop : Nat) : stop = stop := rfl\n'
                    'def f (x : Nat) := x.admit (stop := 1)\n'
                    'stop = tl.num_programs(0)\n'
                    '/-- info: 1 -/\n#guard_msgs in\n#eval 1\n'
                    '/-- error: no -/\n#guard_msgs (error, substring := true) in\n#eval f\n'
                    '/-- info: 1 -/\n#guard_msgs (info, substring := true) in\n#eval 1\n'
                    '/-- error: no -/\n#guard_msgs (error, drop info, substring := true) in\n#eval f\n'
                    # Checked with lake env lean: a `drop info` substring guard lets the warning through.
                    '#guard_msgs (drop info, substring := true) in\n#eval 1\n'
                    # Prose and strings that mention guards or metaprogramming (the first three are on main).
                    '-- Capture parser errors inside elaboration so #guard_msgs can check them;\n'
                    '-- putting unparseable syntax directly after #guard_msgs aborts command parsing.\n'
                    '-- elaboration-level #guard_msgs can intercept the diagnostic.\n'
                    '/-- The prefix loads both operands; a macro or syntax here is prose. -/\n'
                    'def s := "#guard_msgs (substring := true) in macro"\n'
                    'def c := \'"\'\n'
                    'theorem u (h : «syntax» = 1) : True := trivial\n'
                    'def q (l : List Nat) := l.prefix\n'
                    # Lean block comments nest, so this guard is still inside a comment.
                    '/- outer /- inner -/ #guard_msgs (substring := true) in still a comment -/\n')
                # The word in a comment line of a lakefile is fine.
                (root / 'lakefile.toml').write_text('name = "veritile"\n# no sorry here\n')
                allowlist = root / 'allowlist.txt'
                allowlist.write_text('')
                check = ['check_test_sorry.py', '--sources', '--root', str(root), '--allowlist', str(allowlist),
                         '--meta-allowlist', str(allowlist)]
                clean = run(*check)
                self.assertEqual(clean.returncode, 0, clean.stderr)
                (root / relative).parent.mkdir(parents=True, exist_ok=True)
                (root / relative).write_text(text)
                rejected = run(*check)
                self.assertNotEqual(rejected.returncode, 0, case)
                self.assertIn(f'{relative}:', rejected.stderr)
        # An allowlisted declaration may use sorry on a line that names it; other lines may not.
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root / 'tests/lean').mkdir(parents=True)
            (root / 'tests/lean/Owed.lean').write_text('theorem owed : 1 = 2 := sorry\n')
            allowlist = root / 'allowlist.txt'
            allowlist.write_text('tests/lean/Owed.lean\towed\tproof owed by a ticket\n')
            metaprograms = root / 'metaprograms.txt'
            metaprograms.write_text('tests/lean/Owed.lean\ttriv\ta reviewed tactic macro\n')
            check = ['check_test_sorry.py', '--sources', '--root', str(root), '--allowlist', str(allowlist),
                     '--meta-allowlist', str(metaprograms)]
            # An allowlisted macro passes; another one in the same file does not.
            (root / 'tests/lean/Owed.lean').write_text('macro "triv" : tactic => `(tactic| trivial)\n')
            self.assertEqual(run(*check).returncode, 0)
            (root / 'tests/lean/Owed.lean').write_text('macro "triv" : tactic => `(tactic| trivial)\n'
                                                      'macro "triv2" : tactic => `(tactic| trivial)\n')
            rejected = run(*check)
            self.assertIn('tests/lean/Owed.lean:2: macro triv2', rejected.stderr)
            self.assertNotIn('Owed.lean:1:', rejected.stderr)
            # The two lists do not stand in for each other.
            allowlist.write_text('tests/lean/Owed.lean\ttriv2\twrong list\n')
            self.assertIn('macro triv2', run(*check).stderr)
            (root / 'tests/lean/Owed.lean').write_text('theorem triv : 1 = 2 := sorry\n')
            self.assertIn('tests/lean/Owed.lean:1: sorry', run(*check).stderr)
            allowlist.write_text('tests/lean/Owed.lean\towed\tproof owed by a ticket\n')
            (root / 'tests/lean/Owed.lean').write_text('theorem owed : 1 = 2 := sorry\n')
            accepted = run(*check)
            self.assertEqual(accepted.returncode, 0, accepted.stderr)
            (root / 'tests/lean/Owed.lean').write_text('theorem owed : 1 = 2 := sorry\ntheorem owed2 : 1 = 2 := sorry\n')
            rejected = run(*check)
            self.assertIn('tests/lean/Owed.lean:2: sorry', rejected.stderr)
            self.assertNotIn('Owed.lean:1:', rejected.stderr)
        accepted = run('check_test_sorry.py', '--sources')  # this checkout
        self.assertEqual(accepted.returncode, 0, accepted.stderr)

    def test_severity_substring_guards_let_the_warning_through(self):
        # The only substring guards --sources allows; the log scan must still see the sorry.
        relative = 'tests/lean/GateGuardProbe.lean'
        self.probe(relative, '#guard_msgs (error, substring := true) in\n'
                             'theorem veritileErrorGuardProbe : 1 = 2 := by all_goals admit\n'
                             '#guard_msgs (info, substring := true) in\n'
                             'theorem veritileInfoGuardProbe : 1 = 2 := by all_goals admit\n')
        ran = subprocess.run(['lake', 'env', 'lean', relative], cwd=ROOT, text=True, capture_output=True)
        self.assertEqual(ran.returncode, 0, ran.stdout + ran.stderr)
        with tempfile.TemporaryDirectory() as temp:
            log, allowlist = Path(temp) / 'command.log', Path(temp) / 'allowlist.txt'
            log.write_text(ran.stdout + ran.stderr)
            allowlist.write_text('')
            rejected = run('check_test_sorry.py', str(log), '--allowlist', str(allowlist))
            self.assertNotEqual(rejected.returncode, 0, rejected.stdout)
            self.assertIn(f'SORRY\t{relative}\tveritileErrorGuardProbe', rejected.stderr)
            self.assertIn(f'SORRY\t{relative}\tveritileInfoGuardProbe', rejected.stderr)

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
    """check_frozen_base.py on a throwaway repository.

    `main` holds the recorded tables and then moves on (it adds P.later), and the
    branch `pr` commits its edits, so HEAD, the merge base and the tip of main differ.
    """
    STATEMENTS = ('statement\tmodule\tsha256\tsigned\n'
                  f'P.kept\tVeriTile.Dist.Kept\t{"a" * 64}\tbase\n'
                  f'P.other\tVeriTile.Dist.Other\t{"b" * 64}\tbase\n'
                  f'P.staged\tVeriTile.Staging.Dist.Spec\t{"f" * 64}\tbase\n')
    DEFINITIONS = f'definition\tsha256\nP.Def\t{"d" * 64}\n'
    TABLES = Path('documents/dist')

    def git(self, *args):
        subprocess.run(['git', '-c', 'user.name=gate', '-c', 'user.email=gate@example.invalid',
                        '-c', 'commit.gpgsign=false', *args], cwd=self.repo, check=True, capture_output=True)

    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.repo = Path(temp.name)
        self.tsv = self.repo / self.TABLES / 'FrozenStatements.tsv'
        self.definitions = self.repo / self.TABLES / 'FrozenDefinitions.tsv'
        self.tsv.parent.mkdir(parents=True)
        self.git('init', '-q', '-b', 'main')
        self.commit(self.STATEMENTS, self.DEFINITIONS)
        self.git('branch', 'pr')
        self.commit(self.STATEMENTS + f'P.later\tVeriTile.Dist.Later\t{"9" * 64}\tlater\n')
        self.git('checkout', '-q', 'pr')

    def commit(self, statements=None, definitions=None):
        if statements is not None:
            self.tsv.write_text(statements)
        if definitions is not None:
            self.definitions.write_text(definitions)
        self.git('add', '-A')
        self.git('commit', '-qm', 'tables')

    def check(self, override=None, main='main'):
        env = {k: v for k, v in os.environ.items() if k != 'VERITILE_FROZEN_OVERRIDE'}
        if override is not None:
            env['VERITILE_FROZEN_OVERRIDE'] = override
        return run('check_frozen_base.py', '--repo', str(self.repo), *(['--main', main] if main else []), env=env)

    def rejects(self, message, **check):
        rejected = self.check(**check)
        self.assertNotEqual(rejected.returncode, 0, rejected.stdout)
        self.assertIn(message, rejected.stderr)

    def test_deleted_row_fails(self):
        self.commit(self.STATEMENTS.replace(self.STATEMENTS.splitlines()[2] + '\n', ''))
        self.rejects(f'FrozenStatements.tsv: P.other: recorded VeriTile.Dist.Other {"b" * 64} base, now deleted')

    def test_changed_fingerprint_fails(self):
        self.commit(self.STATEMENTS.replace('a' * 64, 'c' * 64))
        self.rejects(f'P.kept: recorded VeriTile.Dist.Kept {"a" * 64} base, now VeriTile.Dist.Kept {"c" * 64} base')
        # What --accept-definitions would do to a recorded definition.
        self.commit(self.STATEMENTS, self.DEFINITIONS.replace('d' * 64, 'e' * 64))
        self.rejects(f'FrozenDefinitions.tsv: P.Def: recorded {"d" * 64}, now {"e" * 64}')

    def test_changed_signed_text_fails(self):
        self.commit(self.STATEMENTS.replace(f'{"a" * 64}\tbase', f'{"a" * 64}\tapproved by the user'))
        self.rejects(f'P.kept: recorded VeriTile.Dist.Kept {"a" * 64} base, '
                     f'now VeriTile.Dist.Kept {"a" * 64} approved by the user')

    def test_module_moves_only_out_of_staging_with_the_same_fingerprint(self):
        # The move to a main target that the contributor guide prescribes.
        self.commit(self.STATEMENTS.replace('VeriTile.Staging.Dist.Spec', 'VeriTile.Dist.Spec'))
        accepted = self.check()
        self.assertEqual(accepted.returncode, 0, accepted.stderr)
        self.assertIn('[moved] P.staged: VeriTile.Staging.Dist.Spec → VeriTile.Dist.Spec', accepted.stdout)
        self.commit(self.STATEMENTS.replace(f'VeriTile.Staging.Dist.Spec\t{"f" * 64}', f'VeriTile.Dist.Spec\t{"c" * 64}'))
        self.rejects(f'P.staged: recorded VeriTile.Staging.Dist.Spec {"f" * 64} base, now VeriTile.Dist.Spec {"c" * 64}')
        # Back into staging, where `sorry` is allowed, is not a move.
        self.commit(self.STATEMENTS.replace('VeriTile.Dist.Kept', 'VeriTile.Staging.Dist.Kept'))
        self.rejects(f'P.kept: recorded VeriTile.Dist.Kept {"a" * 64} base, now VeriTile.Staging.Dist.Kept')

    def test_added_unfilled_row_passes(self):
        self.commit(self.STATEMENTS + 'P.new\tVeriTile.Dist.New\t-\tnew\n')
        accepted = self.check()
        self.assertEqual(accepted.returncode, 0, accepted.stderr)
        self.assertIn('(3 FrozenStatements.tsv row(s), 1 new; 1 FrozenDefinitions.tsv row(s), 0 new)', accepted.stdout)

    def test_override_allows_exactly_the_named_rows(self):
        self.commit(self.STATEMENTS.replace('a' * 64, 'c' * 64), self.DEFINITIONS.replace('d' * 64, 'e' * 64))
        self.assertNotEqual(self.check().returncode, 0)
        self.assertNotEqual(self.check('P.kept').returncode, 0)  # P.Def is still not named
        self.assertNotEqual(self.check('P.kept,P.Def,P.other').returncode, 0)  # P.other did not change
        accepted = self.check('P.kept, P.Def')
        self.assertEqual(accepted.returncode, 0, accepted.stderr)
        self.assertIn("[override] VERITILE_FROZEN_OVERRIDE is set: 'P.kept, P.Def'", accepted.stdout)
        self.assertIn('[override] FrozenStatements.tsv: P.kept: recorded', accepted.stdout)
        self.assertIn('[override] FrozenDefinitions.tsv: P.Def: recorded', accepted.stdout)
        self.commit(self.STATEMENTS, self.DEFINITIONS)
        self.assertIn("[override] VERITILE_FROZEN_OVERRIDE is set: ''", self.check('').stdout)
        self.assertNotIn('[override]', self.check().stdout)

    def test_gate_never_inherits_the_override(self):
        self.assertIn('\nunset VERITILE_FROZEN_OVERRIDE\n', (ROOT / 'scripts/local_gate.sh').read_text())

    def test_symlinked_table_or_directory_fails(self):
        shadow = self.tsv.with_name('Shadow.tsv')
        shadow.write_text(self.STATEMENTS.replace(self.STATEMENTS.splitlines()[1] + '\n', ''))
        self.tsv.unlink()
        self.tsv.symlink_to(shadow.name)
        self.rejects('documents/dist/FrozenStatements.tsv is a symbolic link')
        self.tsv.unlink()
        shadow.rename(self.tsv)
        copy = self.repo / 'documents/copy'
        self.tsv.parent.rename(copy)
        (self.repo / self.TABLES).symlink_to('copy')
        self.rejects('documents/dist is a symbolic link')

    def test_fails_closed_without_main_or_merge_base(self):
        self.rejects('no main ref found among nosuchref', main='nosuchref')
        # A local `main` is not a candidate; this repository has no fork/main or origin/main.
        self.rejects('no main ref found among fork/main, origin/main', main=None)
        self.git('checkout', '-q', '--orphan', 'unrelated')
        self.commit(self.STATEMENTS + '# unrelated history\n')  # a different tree, so not the base commit again
        self.git('checkout', '-q', 'pr')
        self.rejects('no merge base of HEAD and unrelated', main='unrelated')


if __name__ == '__main__':
    unittest.main()
