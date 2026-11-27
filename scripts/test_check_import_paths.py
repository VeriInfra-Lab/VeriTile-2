"""The import-path gate: path-like name components fail in every tracked Lean file."""
import contextlib
import io
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

from unittest import mock

from check_import_paths import check, main

# The re-review of #706: each of these builds against a staging .olean under Lean 4.29.
PATH_LIKE = ('VeriTile.«Staging/ZzProbe»',
             '«VeriTile/Staging».ZzProbe',
             '«VeriTile/Staging/ZzProbe»',
             'VeriTile.«».Staging.ZzProbe',
             'VeriTile.«.».Staging.ZzProbe',
             'bench.«..».VeriTile.Staging.ZzProbe',
             'VeriTile.«Staging/ZzDir».P')


class ImportPaths(unittest.TestCase):
    def tree(self, files):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        root = Path(temp.name)
        subprocess.run(['git', 'init', '-q'], cwd=root, check=True)
        for relative, text in files.items():
            (root / relative).parent.mkdir(parents=True, exist_ok=True)
            (root / relative).write_text(text)
        subprocess.run(['git', 'add', '--', *files], cwd=root, check=True)
        return root

    def test_reviewer_forms_fail_in_any_tracked_file(self):
        for path in ('bench/examples/K/Kernels.lean', 'VeriTile/Dist/Probe.lean', 'tests/lean/Probe.lean'):
            with self.subTest(path=path):
                root = self.tree({path: '\n'.join(f'import {m}' for m in PATH_LIKE) + '\n'})
                self.assertEqual(check(root), (1, [f'{path}:{i}: {m}' for i, m in enumerate(PATH_LIKE, 1)]))
                with contextlib.redirect_stderr(io.StringIO()) as err:
                    self.assertEqual(main(root), 1)
                self.assertIn(f'{path}:1: {PATH_LIKE[0]}', err.getvalue())

    def test_backslash_and_import_all_fail(self):
        root = self.tree({'VeriTile/Probe.lean': 'import VeriTile.«Staging\\ZzProbe»\nimport all VeriTile.«Staging/ZzProbe»\n'})
        self.assertEqual(check(root), (1, ['VeriTile/Probe.lean:1: VeriTile.«Staging\\ZzProbe»',
                                           'VeriTile/Probe.lean:2: VeriTile.«Staging/ZzProbe»']))

    def test_ordinary_and_dotted_atom_names_pass(self):
        root = self.tree({'bench/examples/K/Kernels.lean': '\n'.join([
            'import VeriTile.Triton',
            'import «VeriTile».«Staging».«Dist».«TritonDistProgram»',
            'import «VeriTile.Staging».X',  # one component with a dot: the file VeriTile.Staging/X.lean
            '-- import VeriTile.«Staging/ZzProbe»',
            'def s := "import VeriTile.«Staging/ZzProbe»"',
        ]) + '\n'})
        with contextlib.redirect_stdout(io.StringIO()) as out:
            self.assertEqual(main(root), 0)
        self.assertIn('1 tracked Lean file(s)', out.getvalue())

    def test_empty_scan_fails(self):
        root = self.tree({'README.md': 'no Lean here\n'})
        with contextlib.redirect_stderr(io.StringIO()) as err:
            self.assertEqual(main(root), 1)
        self.assertIn('scanned nothing', err.getvalue())

    def test_pathspec_environment_does_not_hide_files(self):
        path = 'VeriTile/Dist/Deep/Probe.lean'
        root = self.tree({path: 'import VeriTile.«Staging/ZzProbe»\n'})
        for variable in ('GIT_GLOB_PATHSPECS', 'GIT_LITERAL_PATHSPECS'):
            with self.subTest(variable=variable), mock.patch.dict(os.environ, {variable: '1'}):
                self.assertEqual(check(root), (1, [f'{path}:1: VeriTile.«Staging/ZzProbe»']))


if __name__ == '__main__':
    unittest.main()
