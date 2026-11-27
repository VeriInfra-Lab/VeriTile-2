"""The bench staging-import gate: only ALLOWED passes; main targets are check_fork_target.py's."""
import contextlib
import io
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

from unittest import mock

from check_bench_staging_imports import ALLOWED, check, main


class BenchStagingImports(unittest.TestCase):
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

    def test_allowed_module_passes(self):
        root = self.tree({'bench/examples/K/Kernels.lean':
                          f'import VeriTile.Triton\nimport {ALLOWED}\nimport all «VeriTile».Staging.Dist.«TritonDistProgram»\n'})
        with contextlib.redirect_stdout(io.StringIO()) as out:
            self.assertEqual(main(root), 0)
        self.assertIn('1 bench/ Lean file(s)', out.getvalue())

    def test_other_staging_module_fails_with_file_line(self):
        path = 'bench/examples/K/Kernels.lean'
        root = self.tree({path: '\n'.join([
            f'import {ALLOWED}',
            'import VeriTile.Staging.Dist.JudgmentSpec',
            f'import {ALLOWED}.Sub',
            f'import {ALLOWED}X',
            'import VeriTile.Staging',
            'import «VeriTile».«Staging».Dist.EventSpec',
            'import VeriTile.StagingFoo',
            '-- import VeriTile.Staging.Dist.ScopeSpec',
            # Other files whose names lose their distinction if every «» is stripped.
            'import VeriTile.Staging.«Dist.TritonDistProgram»',
            'import VeriTile.Staging.Dist.«TritonDistProgram X»',
            'import all VeriTile.Staging.Dist.JudgmentSpec',
        ]) + '\n'})
        self.assertEqual(check(root), (1, [f'{path}:2: VeriTile.Staging.Dist.JudgmentSpec',
                                           f'{path}:3: {ALLOWED}.Sub',
                                           f'{path}:4: {ALLOWED}X',
                                           f'{path}:5: VeriTile.Staging',
                                           f'{path}:6: «VeriTile».«Staging».Dist.EventSpec',
                                           f'{path}:9: VeriTile.Staging.«Dist.TritonDistProgram»',
                                           f'{path}:10: VeriTile.Staging.Dist.«TritonDistProgram X»',
                                           f'{path}:11: VeriTile.Staging.Dist.JudgmentSpec']))
        with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()) as err:
            self.assertEqual(main(root), 1)
        self.assertIn(f'{path}:2: VeriTile.Staging.Dist.JudgmentSpec', err.getvalue())

    def test_only_bench_is_scanned(self):
        # A main target importing staging, even ALLOWED, is rejected by check_fork_target.py
        # (test_fork_targets.py: test_main_target_cannot_import_staging*), not by this bench rule.
        root = self.tree({'bench/examples/K/Kernels.lean': 'import VeriTile.Triton\n',
                          'VeriTile/Dist/Probe.lean': 'import VeriTile.Staging.Dist.JudgmentSpec\n'})
        self.assertEqual(check(root), (1, []))

    def test_empty_scan_fails(self):
        root = self.tree({'VeriTile/Dist/Probe.lean': 'import VeriTile.Triton\n'})
        with contextlib.redirect_stderr(io.StringIO()) as err:
            self.assertEqual(main(root), 1)
        self.assertIn('scanned nothing', err.getvalue())

    def test_pathspec_environment_does_not_hide_files(self):
        path = 'bench/examples/K/Proofs/Deep.lean'
        root = self.tree({path: 'import VeriTile.Staging.Dist.JudgmentSpec\n'})
        for variable in ('GIT_GLOB_PATHSPECS', 'GIT_LITERAL_PATHSPECS'):
            with self.subTest(variable=variable), mock.patch.dict(os.environ, {variable: '1'}):
                self.assertEqual(check(root), (1, [f'{path}:1: VeriTile.Staging.Dist.JudgmentSpec']))


if __name__ == '__main__':
    unittest.main()
