"""The C3 name gate: real references fail, comments, strings and JudgmentSpec.lean pass."""
import contextlib
import io
from pathlib import Path
import subprocess
import tempfile
import unittest

from check_forbidden_references import EXEMPT, REMOVAL, check, main


class ForbiddenReferences(unittest.TestCase):
    def tree(self, files, untracked=None):
        """A Git repository with `files` in its index and `untracked` only written."""
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        root = Path(temp.name)
        subprocess.run(['git', 'init', '-q'], cwd=root, check=True)
        for relative, text in {**files, **(untracked or {})}.items():
            (root / relative).parent.mkdir(parents=True, exist_ok=True)
            (root / relative).write_text(text)
        if files:
            subprocess.run(['git', 'add', '--', *files], cwd=root, check=True)
        return root

    def test_reference_under_veritile_fails_with_file_line(self):
        root = self.tree({'VeriTile/Dist/Probe.lean': 'import X\n\nexample := implementsAll_of_canonical\n'})
        out, err = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            self.assertEqual(main(root), 1)
        self.assertIn('VeriTile/Dist/Probe.lean:3: implementsAll_of_canonical', err.getvalue())
        self.assertIn(REMOVAL, err.getvalue())

    def test_reference_under_tests_fails(self):
        root = self.tree({'tests/lean/dist/Probe.lean': 'theorem t := detRaceFree_complete_eq_canonical\n'})
        self.assertEqual(check(root), ['tests/lean/dist/Probe.lean:1: detRaceFree_complete_eq_canonical'])

    def test_qualified_opened_and_escaped_references_fail(self):
        root = self.tree({'tests/lean/Probe.lean': '\n'.join([
            'example := VeriTile.Dist.implementsAll_of_canonical',
            'open VeriTile.Dist (detRaceFree_scopeConsistent_complete_eq_canonical)',
            'example := «implementsAll_of_canonical»',
            '#check `VeriTile.Dist.implementsAll_of_canonical',
            'example := (implementsAll_of_canonical).mp',
        ]) + '\n'})
        self.assertEqual([hit.split(':')[1] for hit in check(root)], ['1', '2', '3', '4', '5'])

    def test_comments_docstrings_and_strings_pass(self):
        root = self.tree({'tests/lean/Probe.lean': '\n'.join([
            '-- implementsAll_of_canonical',
            'def x := 1 -- detRaceFree_complete_eq_canonical',
            '/- outer /- detRaceFree_scopeConsistent_complete_eq_canonical -/',
            '   still comment: implementsAll_of_canonical -/',
            '/-- The statement of `detRaceFree_complete_eq_canonical` does not hold. -/',
            'theorem t : True := trivial',
            'def s := "implementsAll_of_canonical \\" detRaceFree_complete_eq_canonical"',
        ]) + '\n'})
        self.assertEqual(check(root), [])

    def test_judgment_spec_is_exempt_only_at_its_path(self):
        text = 'theorem implementsAll_of_canonical := detRaceFree_scopeConsistent_complete_eq_canonical\n'
        root = self.tree({EXEMPT: text, 'tests/lean/JudgmentSpec.lean': text})
        self.assertEqual(check(root), ['tests/lean/JudgmentSpec.lean:1: implementsAll_of_canonical',
                                       'tests/lean/JudgmentSpec.lean:1: detRaceFree_scopeConsistent_complete_eq_canonical'])

    def test_longer_identifiers_do_not_match(self):
        root = self.tree({'VeriTile/Probe.lean': '\n'.join([
            "theorem implementsAll_of_canonical' := 0",
            'theorem my_implementsAll_of_canonical := 0',
            'theorem implementsAll_of_canonical_v2 := 0',
            'theorem implementsAll_of_canonical₁ := 0',
            'theorem implementsAll_of_canonical? := 0',
            'theorem xdetRaceFree_complete_eq_canonical := 0',
        ]) + '\n'})
        self.assertEqual(check(root), [])

    def test_bench_and_scripts_are_scanned(self):
        root = self.tree({'bench/examples/Probe/Proofs/C3.lean': 'example := implementsAll_of_canonical\n',
                          'scripts/fixtures/Probe.lean': 'example := detRaceFree_complete_eq_canonical\n'})
        self.assertEqual(check(root), ['bench/examples/Probe/Proofs/C3.lean:1: implementsAll_of_canonical',
                                       'scripts/fixtures/Probe.lean:1: detRaceFree_complete_eq_canonical'])

    def test_untracked_files_are_not_scanned(self):
        text = 'example := implementsAll_of_canonical\n'
        root = self.tree({'tests/lean/Clean.lean': 'def x := 1\n'},
                         untracked={'.lake/packages/dep/Dep.lean': text, 'tests/lean/Scratch.lean': text})
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            self.assertEqual(main(root), 0)
        self.assertIn(REMOVAL, out.getvalue())

if __name__ == '__main__':
    unittest.main()
