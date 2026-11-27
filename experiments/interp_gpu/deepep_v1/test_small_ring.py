"""CPU reference bundle for the small-ring dispatch/combine experiment."""
from dataclasses import dataclass
import contextlib
import io
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import dispatch_variant
import harness
import judge
import judge_variant
from gpurun import run


def first_blocks(selected, capacity):
    """Start each sender before its receiver, whose queue head is initially zero."""
    dispatch_wait = None
    tail = 0
    position = 0
    while position < len(selected):
        threshold = tail + 24 - capacity  # DD 334–338 reserves a full send block.
        if threshold > 0:
            dispatch_wait = threshold
            break
        before = tail
        while position < len(selected) and tail - before < 24:
            tail += selected[position]
            position += 1
    count = sum(selected)
    for tail in range(0, count, 10):
        threshold = tail + min(10, count - tail) - capacity  # DC 173–179 reserves the actual round.
        if threshold > 0:
            return dispatch_wait, threshold
    return dispatch_wait, None


def cpu_reference(rank, ranks, inputs, outputs, launch):
    x, idx, weights = (judge.nested(inputs[name]) for name in ('x', 'topk_idx', 'topk_weights'))
    ring = launch['ring']
    assert ring['num_sms'] == 2  # Each source's entire input belongs to channel 0.
    local = launch['num_experts'] // ranks
    for dest in range(ranks):
        selected = [any(e >= 0 and e // local == dest for e in row) for row in idx[rank]]
        print('cpu-head-wait', rank, dest, sum(selected), *first_blocks(selected, ring['recv_tokens']), flush=True)
    values = judge.expected(x, idx, weights, launch['num_experts'], launch['scale'])[rank]
    for name, blank in list(outputs.items()):
        outputs[name] = judge.fill(blank, values[name])
    # This is a CPU fixture for the judge. GPU ranks emit these fields from live objects.
    pins = json.loads((HERE / 'source-sha256.json').read_text())
    print(dispatch_variant.SOURCE_RECORD + json.dumps({'rank': rank, 'files': {**pins['original'], **pins[judge_variant.NAME]}}))
    print(f'deepep-ring rank={rank} channels=1 dispatch=24/24 combine=10/24')


class SmallRing(unittest.TestCase):
    def test_public_cli_rejects_empty_or_missing_results(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / 'DONE').touch()
            # Invoke the actual script with a temporary batch table. The public CLI otherwise
            # accepts only the three committed batch names, all of which have at least one test.
            (root / judge_variant.NAME).mkdir()
            for tests in ([], None):
                batch = {'batch_id': judge_variant.NAME}
                if tests is not None:
                    batch['tests'] = tests
                (root / judge_variant.NAME / 'batch.json').write_text(json.dumps(batch))
                (root / 'manifest.json').write_text(json.dumps({'batch_id': judge_variant.NAME, 'tests': {}}))
                code = ('import pathlib,runpy,sys;sys.path.insert(0,sys.argv.pop(1));import judge;'
                        'judge.BATCHES=pathlib.Path(sys.argv[1]);runpy.run_path(str(pathlib.Path(judge.__file__)'
                        '.with_name("judge_variant.py")), run_name="__main__")')
                result = subprocess.run([sys.executable, '-B', '-c', code, str(HERE), tmp], text=True,
                                        capture_output=True)
                self.assertNotEqual(result.returncode, 0, result.stdout)
                self.assertIn('no test results', result.stderr)

    def test_public_cli_rejects_missing_manifest_results(self):
        with tempfile.TemporaryDirectory() as tmp:
            bundle = Path(tmp)
            (bundle / 'DONE').touch()
            for fields, message in (({}, 'Missing result data'), ({'tests': {}}, 'missing test results')):
                (bundle / 'manifest.json').write_text(json.dumps({'batch_id': judge_variant.NAME, **fields}))
                proc = subprocess.run([sys.executable, '-B', str(HERE / 'judge_variant.py'), tmp],
                                      text=True, capture_output=True)
                self.assertNotEqual(proc.returncode, 0)
                self.assertIn(message, proc.stderr)

    def test_recorded_input_judgment_prints_the_limit(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / 'DONE').touch()
            batch = run.load_batch(judge.BATCHES / judge_variant.NAME)
            (root / 'manifest.json').write_text(json.dumps({'batch_id': batch['batch_id'],
                'tests': {test['id']: 'timeout' for test in batch['tests']}}))
            cli = subprocess.run([sys.executable, '-B', str(HERE / 'judge_variant.py'), tmp], text=True, capture_output=True)
            self.assertEqual(cli.returncode, 1)
            self.assertIn(judge_variant.RECORDED_LIMIT, cli.stdout)
            self.assertIn(judge_variant.RECORDED_LIMIT, (HERE / 'DispatchVariant.md').read_text())

    def test_config_reaches_the_buffer_and_both_kernels(self):
        @dataclass
        class Config:
            num_sms: int
            num_max_nvl_chunked_send_tokens: int
            num_max_nvl_chunked_recv_tokens: int

        module = mock.Mock()
        module.Config.get_dispatch_config.return_value = Config(20, 24, 256)
        module.Config.get_combine_config.return_value = Config(20, 10, 256)
        group, ctor = mock.Mock(), mock.Mock()
        group.size.return_value, group.rank.return_value = 2, 1
        ctor.side_effect = lambda *args, **cfg: mock.Mock(num_channels=1, **cfg)
        test, = run.load_batch(judge.BATCHES / judge_variant.SMALL_RING)['tests']
        with mock.patch.dict(sys.modules, {'deepep_utils': module}), contextlib.redirect_stdout(io.StringIO()) as log:
            harness.make_buffer(ctor, group, 2, 64, test['launch'])
        ctor.set_num_sms.assert_called_once_with(2)
        ctor.assert_called_once_with(group, 2**30, 2, 8, 64, dispatch_cfg=Config(2, 24, 24), combine_cfg=Config(2, 10, 24))
        self.assertEqual(log.getvalue().strip(), 'deepep-ring rank=1 channels=1 dispatch=24/24 combine=10/24')

    def test_cpu_bundle_shows_the_positive_waits_and_matches_recorded_tensors(self):
        batch = run.load_batch(judge.BATCHES / judge_variant.SMALL_RING)
        batch['requires'] = {}
        test, = batch['tests']
        self.assertEqual(test['entry'], 'experiments/interp_gpu/deepep_v1/dispatch_variant.py::run')
        test.update(frontend='mock', launcher='mock', entry='test_small_ring.py::cpu_reference')
        with tempfile.TemporaryDirectory() as tmp:
            batch_dir, bundle = Path(tmp) / 'batch', Path(tmp) / 'bundle'
            batch_dir.mkdir()
            (batch_dir / 'batch.json').write_text(json.dumps(batch))
            run.run_batch(batch_dir, bundle, env={'gpus': [], 'versions': {}}, root=HERE)
            log = bundle / test['id'] / 'stdout.log'
            contents = log.read_text()
            # Original source, dispatch destination, number routed, DD threshold, reverse DC threshold.
            for line in ('0 0 29 24 5', '0 1 24 None None', '1 0 29 24 5', '1 1 28 24 4'):
                self.assertEqual(contents.count('cpu-head-wait ' + line), 2, contents)
            cli = [sys.executable, '-B', str(HERE / 'judge_variant.py'), str(bundle), '--batch', judge_variant.SMALL_RING]
            result = subprocess.run(cli, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stderr + result.stdout)
            self.assertIn('intranode/rank_weighted: equal', result.stdout)
            self.assertNotIn('thresholds are negative', result.stdout)
            log.write_text(contents.replace('channels=1', 'channels=10', 1))
            wrong = subprocess.run(cli, capture_output=True, text=True)
            self.assertNotEqual(wrong.returncode, 0)
            self.assertIn('incorrect executed ring configuration', wrong.stdout)
