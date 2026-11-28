"""Regression checks for the homepage proof fingerprint."""
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

spec = importlib.util.spec_from_file_location(
    'record_home_demo', Path(__file__).with_name('record-home-demo.py'))
recorder = importlib.util.module_from_spec(spec)
spec.loader.exec_module(recorder)


class FingerprintTests(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        self.recorder_path = self.write('site/scripts/record-home-demo.py',
                                        Path(recorder.__file__).read_text())
        self.project = recorder.ROOT
        sources = tuple(self.write(path.relative_to(self.project), '')
                        for path in recorder.PROOF_SOURCES)
        self.write('bench/examples/VectorAdd/RealCorrect.lean',
                   'import Mathlib\nimport VeriTile.Direct\n')
        self.write('VeriTile/Direct.lean', '/-\nimport VeriTile.Unused\n-/\nimport VeriTile.Transitive\n')
        self.write('VeriTile/Transitive.lean', 'def checked : Nat := 1\n')
        self.write('VeriTile/Unused.lean', 'def unrelated : Nat := 1\n')
        for name in ('lean-toolchain', 'lake-manifest.json'):
            self.write(name, 'fixture\n')
        for name in ('lakefile.toml', 'library/lakefile.toml'):
            self.write(name, 'name = "fixture"\n')
        self.write('scripts/local_gate.sh', '#!/bin/sh\nset -e\n')
        overrides = patch.multiple(recorder, ROOT=self.root, PROOF_SOURCES=sources)
        overrides.start()
        self.addCleanup(overrides.stop)

    def write(self, name, content):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content)
        return path

    def check(self):
        # Run the public CLI in the fixture and import its shared Python scanner from the project.
        return subprocess.run([sys.executable, str(self.recorder_path), '--check'],
                              cwd=self.root, env={**os.environ, 'PYTHONPATH': str(self.project)},
                              text=True, capture_output=True)

    def seed_record(self):
        self.write('site/src/lib/vector-add-record.json',
                   json.dumps({'fingerprint': recorder.fingerprint()}))
        result = self.check()
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_registering_unrelated_test_leaves_record_fresh(self):
        self.seed_record()
        self.write('tests/lean/HomepageUnrelated.lean', 'example : True := True.intro\n')
        self.write('VeriTile/Unused.lean', 'def unrelated : Nat := 2\n')
        for name in ('lakefile.toml', 'library/lakefile.toml'):
            with (self.root / name).open('a') as config:
                config.write('[[lean_lib]]\nname = "FixtureTests"\nroots = ["tests.lean.HomepageUnrelated"]\n')
        with (self.root / 'scripts/local_gate.sh').open('a') as gate:
            gate.write('lake build tests.lean.HomepageUnrelated\n')
        result = self.check()
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_changing_transitive_import_makes_record_stale(self):
        self.seed_record()
        self.write('VeriTile/Transitive.lean', 'def checked : Nat := 2\n')
        result = self.check()
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn('records are stale', result.stderr)

    def test_proof_sources_and_pinned_inputs_change_fingerprint(self):
        initial = recorder.fingerprint()
        for name in ('bench/examples/VectorAdd/RealCorrect.lean', 'VeriTile/Direct.lean',
                     'VeriTile/Transitive.lean', 'lean-toolchain', 'lake-manifest.json',
                     'site/scripts/record-home-demo.py'):
            with self.subTest(name=name):
                path = self.root / name
                original = path.read_text()
                self.write(name, original + '\n-- Change to a tracked proof input.\n')
                self.assertNotEqual(recorder.fingerprint(), initial)
                self.write(name, original)
