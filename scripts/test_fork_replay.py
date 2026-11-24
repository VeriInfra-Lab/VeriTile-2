#!/usr/bin/env python3
"""Orchestration of check_fork_target.replay without Lean: order, all failures, overlap."""
import contextlib
import io
from pathlib import Path
import sys
import tempfile
import threading
import time
import unittest
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parent))
import check_fork_target  # noqa: E402


class Replay(unittest.TestCase):
    def run_replay(self, files, build_fails=(), rejected=(), delay=0.0, jobs=4):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        active, peak, lock = [0], [0], threading.Lock()
        lake = []

        def stage(workspace, source, trust):
            self.assertTrue(trust)
            return {'label': str(source), 'module': 'M.' + str(source), 'judge': Path(temp.name),
                    'state': {'logs': temp.name}}

        def build(job):
            if job['label'] in build_fails:
                raise ValueError(f'{job["label"]}: elaboration/inventory failed')

        def finish(job):
            with lock:
                active[0] += 1
                peak[0] = max(peak[0], active[0])
            time.sleep(delay)
            with lock:
                active[0] -= 1
            return {'accepted': job['label'] not in rejected}

        def report_lines(job, report):
            if not report['accepted']:
                raise ValueError(f'{job["label"]}: comparator rejected')
            return [f'Comparator: {job["label"]}: accepted']

        out = io.StringIO()
        with mock.patch.multiple(check_fork_target.check_comparator, stage=stage, build=build,
                                 finish=finish, report_lines=report_lines), \
                mock.patch.object(check_fork_target.subprocess, 'run',
                                  side_effect=lambda command, **_: lake.append(command)), \
                mock.patch.dict(check_fork_target.os.environ, {'VERITILE_REPLAY_WORKSPACE': temp.name}), \
                contextlib.redirect_stdout(out):
            try:
                check_fork_target.replay('Lib', files, jobs=jobs)
                error = None
            except ValueError as raised:
                error = str(raised)
        return out.getvalue().splitlines(), error, peak[0], lake

    def test_one_lake_build_and_output_in_file_order(self):
        lines, error, _, lake = self.run_replay(['a', 'b', 'c'], delay=0.01)
        self.assertIsNone(error)
        self.assertEqual(lines, [f'Comparator: {f}: accepted' for f in 'abc'])
        self.assertEqual(lake, [['lake', 'build', 'M.a', 'M.b', 'M.c']])

    def test_every_failure_is_reported_in_file_order(self):
        lines, error, _, _ = self.run_replay(['a', 'b', 'c', 'd'], build_fails={'c'}, rejected={'a'})
        self.assertEqual(lines, ['Comparator: b: accepted', 'Comparator: d: accepted'])
        self.assertIn('2 file(s) failed', error)
        self.assertLess(error.index('a: comparator rejected'), error.index('c: elaboration'))

    def test_comparator_runs_overlap(self):
        _, error, peak, _ = self.run_replay(['a', 'b', 'c', 'd'], delay=0.2, jobs=4)
        self.assertIsNone(error)
        self.assertGreater(peak, 1)


if __name__ == '__main__':
    unittest.main()
