#!/usr/bin/env python3
"""Self-test of the DeepEP version 1 request: the judge, the batch and the harness's calls. No GPU, torch or tilelang needed.

    python3 -B -m unittest discover -s experiments/interp_gpu/deepep_v1 -p 'test_*.py'
"""
import contextlib
import hashlib
import io
import json
import os
import re
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parent))
import judge
import judge_variant
import dispatch_variant
from judge import ROOT
from gpurun import run
from interp import gen_inputs, tensorfile
from interp.tensorfile import Tensor

BATCH = judge.BATCHES / 'deepep-v1-intranode-001'
TESTS = json.loads((BATCH / 'batch.json').read_text())['tests']


class Expected(unittest.TestCase):
    def test_hand_computed_routing(self):
        # Two ranks with two experts each; rank 0 owns experts 0 and 1.
        x = [[[1.0], [2.0], [3.0]], [[4.0], [5.0], [6.0]]]
        topk_idx = [[[0, 2], [3, -1], [-1, -1]], [[1, 2], [2, 3], [-1, 1]]]
        topk_weights = [[[0.5, 0.25], [0.75, 9.0], [8.0, 7.0]], [[1.5, 2.5], [3.5, 4.5], [5.5, 6.5]]]
        rank0, rank1 = judge.expected(x, topk_idx, topk_weights, 4, [1, -0.5])
        self.assertEqual(rank0, {
            'is_token_in_rank': [[1, 1], [0, 1], [0, 0]],
            'num_tokens_per_rank': [1, 2],
            'num_tokens_per_expert': [1, 0, 1, 1],
            'recv_x': [[1.0], [4.0], [6.0]],  # token 0 of rank 0, then tokens 0 and 2 of rank 1
            'recv_src_idx': [0, 0, 2],
            'recv_topk_idx': [[0, -1], [1, -1], [-1, 1]],
            'recv_topk_weights': [[0.5, 0.0], [1.5, 0.0], [0.0, 6.5]],
            'combined_x': [[0.5], [-1.0], [0.0]],  # both ranks, rank 1 alone, no rank
            'combined_topk_weights': [[0.5, 0.25], [0.75, 0.0], [0.0, 0.0]],
        })
        self.assertEqual(rank1, {
            'is_token_in_rank': [[1, 1], [0, 1], [1, 0]],
            'num_tokens_per_rank': [2, 2],
            'num_tokens_per_expert': [0, 2, 2, 1],
            'recv_x': [[1.0], [2.0], [4.0], [5.0]],  # by source rank first: token 1 of rank 0 before token 0 of rank 1
            'recv_src_idx': [0, 1, 0, 1],
            'recv_topk_idx': [[-1, 0], [1, -1], [-1, 0], [0, 1]],
            'recv_topk_weights': [[0.0, 0.25], [0.75, 0.0], [0.0, 2.5], [3.5, 4.5]],
            'combined_x': [[2.0], [-2.5], [6.0]],
            'combined_topk_weights': [[1.5, 2.5], [3.5, 4.5], [0.0, 6.5]],
        })

    def test_a_value_the_dtype_cannot_hold_is_refused(self):
        self.assertEqual(judge.encode('bf16', -0.5), bytes.fromhex('00bf'))
        self.assertEqual(judge.encode('int64', -1), b'\xff' * 8)
        with self.assertRaisesRegex(ValueError, 'not exact in bf16'):
            judge.encode('bf16', 1 + 2 ** -10)  # would need a rounding rule


class Batch(unittest.TestCase):
    def test_gpurun_loads_it_and_the_inputs_are_the_pinned_ones(self):
        batch = run.load_batch(BATCH)
        self.assertEqual((batch['mode'], batch['requires']), ('dist', {'sm': 90, 'gpus': 2, 'env': 'tilescale-deepep'}))
        for test in batch['tests']:
            self.assertEqual((test['ranks'], test['launcher']), (2, 'tilescale-deepep'))
            self.assertTrue((ROOT / test['entry'].partition('::')[0]).is_file())
            for spec in test['inputs']:
                self.assertEqual(gen_inputs.generate(spec['dtype'], spec['shape'], spec['gen']).sha256(), spec['sha256'])

    def test_variant_request_uses_same_inputs_launch_and_outputs(self):
        original = run.load_batch(judge.BATCHES / 'deepep-v1-intranode-002')
        variant = run.load_batch(judge.BATCHES / judge_variant.NAME)
        self.assertEqual(original['requires'], variant['requires'])
        self.assertEqual(len(variant['tests']), 2)
        for before, after in zip(original['tests'], variant['tests']):
            self.assertEqual({**before, 'entry': after['entry']}, after)
            self.assertEqual(after['entry'], 'experiments/interp_gpu/deepep_v1/dispatch_variant.py::run')
            entry = run.load_entry(after['entry'], ROOT)
            with mock.patch('gpurun.dist.deepep_port', return_value=ROOT / dispatch_variant.PORT), \
                    self.assertRaisesRegex(ValueError, 'expected ' + dispatch_variant.PIN):
                entry(0, 2, {}, {}, after['launch'])

    def test_combine_request_uses_both_stages_on_the_same_cases(self):
        dispatch = run.load_batch(judge.BATCHES / judge_variant.NAME)
        combined = run.load_batch(judge.BATCHES / 'deepep-v1-variant-intranode-002')
        self.assertEqual(dispatch['requires'], combined['requires'])
        self.assertEqual(len(combined['tests']), 2)
        for left, right in zip(dispatch['tests'], combined['tests']):
            self.assertEqual({**left, 'entry': left['entry'] + '_combine'}, right)
            self.assertTrue(callable(run.load_entry(right['entry'], ROOT)))

    def test_saved_cuda_orders_each_shared_object_at_each_observed_site(self):
        cuda = Path(__file__).with_name('combine-cta.cu').read_text()
        access = re.compile(r'tl::(ld|st)<Semantic::(\w+), Scope::(\w+), [^>]+>\(\(&\((\w+)\[')
        for name, size, loads, stores in [('warp_retired', 24, 2, 1), ('warp_channel_head_idx', 48, 1, 1),
                                          ('shared_channel_tail_idx', 32, 2, 1)]:
            self.assertIn(f'__shared__ int {name}[{size}];', cuda)
            actual = [(op, sem, scope) for op, sem, scope, operand in access.findall(cuda) if operand == name]
            self.assertCountEqual(actual, [('ld', 'ACQUIRE', 'CTA')] * loads + [('st', 'RELEASE', 'CTA')] * stores)

    def test_rank_hashes_the_files_materialized_by_git_apply(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / 'fixture'
            checkout = root / 'checkout'
            port = checkout / dispatch_variant.PORT
            port.mkdir(parents=True)
            (port / 'kernel.py').write_bytes(b'before\n')
            subprocess.run(['git', 'init', '-q', str(checkout)], check=True)
            git = ['git', '-C', str(checkout)]
            subprocess.run([*git, 'add', '.'], check=True)
            subprocess.run([*git, '-c', 'user.name=Fixture', '-c', 'user.email=fixture@example.invalid',
                            'commit', '-qm', 'source fixture'], check=True)
            pin = subprocess.check_output([*git, 'rev-parse', 'HEAD'], text=True).strip()
            (root / 'dispatch-release.patch').write_text(
                '--- a/kernel.py\n+++ b/kernel.py\n@@ -1 +1 @@\n-before\n+after\n')
            original = {'kernel.py': hashlib.sha256(b'before\n').hexdigest()}
            changed = {'kernel.py': hashlib.sha256(b'after\n').hexdigest()}
            actual_run = subprocess.run

            def missing_patch(command, **kwargs):
                if command[:2] == ['git', 'apply']:
                    return subprocess.CompletedProcess(command, 0)
                return actual_run(command, **kwargs)

            for apply_patch in (True, False):
                log = io.StringIO()
                with self.subTest(applied=apply_patch), mock.patch.object(dispatch_variant, 'PIN', pin), \
                        mock.patch.object(dispatch_variant, 'HERE', root), \
                        mock.patch('gpurun.dist.deepep_port', return_value=port), \
                        mock.patch('gpurun.run.load_entry', return_value=mock.Mock()), \
                        mock.patch('subprocess.run', actual_run if apply_patch else missing_patch), \
                        contextlib.redirect_stdout(log):
                    dispatch_variant.run(0, 1, {}, {}, {})
                (root / 'stdout.log').write_text('== repeat 0 ==\n' + log.getvalue())
                error = judge_variant.source_error(root, {'ranks': 1, 'repeats': 1}, original, changed)
                if apply_patch:
                    self.assertIsNone(error)
                else:
                    self.assertIn('kernel.py has the original hash', error)

    def test_inputs_stay_where_the_port_is_documented(self):
        for test in TESTS:
            shapes = {spec['name']: spec['shape'] for spec in test['inputs'] + test['outputs']}
            ranks, tokens, hidden = shapes['x']
            experts, local = test['launch']['num_experts'], test['launch']['num_experts'] // ranks
            self.assertEqual((ranks, experts % ranks, hidden % 8), (test['ranks'], 0, 0))
            self.assertEqual(shapes['recv_x'], [ranks * tokens, hidden])  # room for every token of every rank
            spec = next(spec for spec in test['inputs'] if spec['name'] == 'topk_idx')
            for rows in judge.nested(gen_inputs.generate(spec['dtype'], spec['shape'], spec['gen'])):
                chosen = [[expert for expert in row if expert >= 0] for row in rows]
                self.assertTrue(all(-1 <= expert < experts for row in rows for expert in row))
                self.assertTrue(all(len(set(row)) == len(row) for row in chosen))  # a top-k never repeats an expert
                # A token for no rank, for each rank alone and for both.
                self.assertEqual({frozenset(expert // local for expert in row) for row in chosen},
                                 {frozenset(), frozenset({0}), frozenset({1}), frozenset({0, 1})})
            # One round per channel in dispatch and combine: a tail index is published once.
            self.assertLessEqual(-(-tokens // 10), 10)


# What a rank of a correct port returns, as an entry of gpurun's CPU mock.
ENTRY = '''
import sys
sys.path.insert(0, {here!r})
import judge

def run(rank, ranks, inputs, outputs, launch):
    values = judge.expected(*(judge.nested(inputs[name]) for name in ('x', 'topk_idx', 'topk_weights')),
                            launch['num_experts'], launch['scale'])[rank]
    for name, blank in list(outputs.items()):
        outputs[name] = judge.fill(blank, values[name])
'''


class Judge(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        """The bundle gpurun itself writes for the batch when every rank returns the reference."""
        temp = tempfile.TemporaryDirectory()
        cls.addClassCleanup(temp.cleanup)
        cls.written = Path(temp.name)
        (cls.written / 'entry.py').write_text(ENTRY.format(here=str(Path(__file__).resolve().parent)))
        batch = json.loads((BATCH / 'batch.json').read_text())
        batch['requires'] = {}
        for test in batch['tests']:
            test.update(frontend='mock', launcher='mock', entry='entry.py::run')
        (cls.written / 'batch').mkdir()
        (cls.written / 'batch/batch.json').write_text(json.dumps(batch))
        run.run_batch(cls.written / 'batch', cls.written / 'bundle', env={'gpus': [], 'versions': {}}, root=cls.written)

    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.bundle = shutil.copytree(self.written / 'bundle', Path(temp.name) / 'bundle')

    def edit(self, name, change):
        text = json.loads((self.bundle / name).read_text())
        change(text)
        (self.bundle / name).write_text(json.dumps(text))

    def plant(self, test, key, change, repeats=2):
        """Replace the stored value of one output by `change(reference bytes)` for `repeats` of the two repeats."""
        (sha256,) = json.loads((self.bundle / test['id'] / 'meta.json').read_text())['distinct'][key]
        right = tensorfile.read(self.bundle / test['id'] / 'out' / key / (sha256 + '.tensor'))
        wrong = Tensor(right.dtype, right.shape, change(right.data))
        tensorfile.write(self.bundle / test['id'] / 'out' / key / (wrong.sha256() + '.tensor'), wrong)
        self.edit(test['id'] + '/meta.json', lambda meta: meta['distinct'].update(
            {key: {wrong.sha256(): repeats, **({sha256: 2 - repeats} if repeats < 2 else {})}}))

    def verdicts(self):
        return {entry['test']: entry['verdict'] for entry in judge.judge(BATCH, self.bundle)}

    def test_reference_bundle_is_equal(self):
        self.assertEqual(self.verdicts(), {'intranode/identity': 'equal', 'intranode/rank_weighted': 'equal'})

    def candidate(self, name=judge_variant.NAME):
        # These tensor bytes come from gpurun's CPU reference entry. Supply the source
        # evidence of the named candidate explicitly for isolated judge tests.
        self.edit('manifest.json', lambda m: m.update(batch_id=name))
        pins = json.loads(Path(judge_variant.__file__).with_name('source-sha256.json').read_text())
        files = {**pins['original'], **pins[name]}
        for test in TESTS:
            lines = []
            for repeat in range(test['repeats']):
                lines.append(f'== repeat {repeat} ==')
                for rank in range(test['ranks']):
                    lines.append(dispatch_variant.SOURCE_RECORD + json.dumps({'rank': rank, 'files': files}))
            (self.bundle / test['id'] / 'stdout.log').write_text('\n'.join(lines) + '\n')

    def test_original_files_and_incomplete_source_records_reject_equal_tensors(self):
        path = self.bundle / TESTS[0]['id'] / 'stdout.log'
        pins = json.loads(Path(judge_variant.__file__).with_name('source-sha256.json').read_text())
        for problem in ('original', 'unknown hash', 'missing file', 'extra file', 'duplicate rank', 'missing repeat'):
            with self.subTest(problem=problem):
                self.candidate()
                lines = path.read_text().splitlines()
                files = {**pins['original'], **pins[judge_variant.NAME]}
                if problem == 'original':
                    files = pins['original']
                elif problem == 'unknown hash':
                    files['intranode/dispatch.py'] = '0' * 64
                elif problem == 'missing file':
                    files.pop('buffer.py')
                elif problem == 'extra file':
                    files['extra.py'] = '0' * 64
                lines[-1] = dispatch_variant.SOURCE_RECORD + json.dumps({'rank': 1, 'files': files})
                if problem == 'duplicate rank':
                    lines[-1] = lines[-2]
                if problem == 'missing repeat':
                    lines = lines[:3]
                path.write_text('\n'.join(lines) + '\n')
                results = judge_variant.compare_recorded(self.bundle)
                self.assertEqual([r['verdict'] for r in results], ['different', 'equal'])
                self.assertEqual([d['output'] for d in results[0]['differences']], ['source hashes'])

    def test_variant_rejects_bad_metadata_with_matching_tensors(self):
        self.candidate()
        path = self.bundle / TESTS[0]['id'] / 'meta.json'
        valid = path.read_text()
        for field in ('status', 'ranks', 'repeats', 'inputs', 'distinct'):
            with self.subTest(field=field):
                meta = json.loads(valid)
                if field == 'inputs':
                    meta[field]['x']['sha256'] = '0' * 64
                elif field == 'distinct':
                    meta[field]['rank0/unexpected'] = {}
                else:
                    meta[field] = {'status': 'timeout', 'ranks': 3, 'repeats': 1}[field]
                path.write_text(json.dumps(meta))
                results = judge_variant.compare_recorded(self.bundle)
                self.assertEqual([r['verdict'] for r in results], ['different', 'equal'])
                self.assertEqual([d['output'] for d in results[0]['differences']], ['metadata'])

    def test_candidate_matches_recorded_gpu_hashes_and_repeat_counts(self):
        self.candidate()
        self.assertEqual([r['verdict'] for r in judge_variant.compare_recorded(self.bundle)], ['equal', 'equal'])
        key = 'rank1/combined_x'
        self.edit('intranode/rank_weighted/meta.json',
                  lambda m: m['distinct'][key].update({next(iter(m['distinct'][key])): 1}))
        # The existing value-only oracle still accepts the bytes. The recorded-run check notices the lost repeat.
        self.assertEqual(judge.judge(judge.BATCHES / judge_variant.NAME, self.bundle)[1]['verdict'], 'equal')
        result = judge_variant.compare_recorded(self.bundle)[1]
        self.assertEqual((result['verdict'], result['differences'][0]['output']), ('different', key))

    def test_combined_request_replays_the_same_recorded_tensors(self):
        name = 'deepep-v1-variant-intranode-002'
        self.candidate(name)
        results = judge_variant.compare_recorded(self.bundle, judge.BATCHES / name)
        self.assertEqual([r['verdict'] for r in results], ['equal', 'equal'])

    def test_combined_request_rejects_dispatch_only_sources(self):
        self.candidate()
        name = 'deepep-v1-variant-intranode-002'
        self.edit('manifest.json', lambda m: m.update(batch_id=name))
        results = judge_variant.compare_recorded(self.bundle, judge.BATCHES / name)
        for result in results:
            self.assertEqual(result['verdict'], 'different')
            self.assertEqual([d['output'] for d in result['differences']], ['source hashes'])

    def test_recorded_comparison_detects_one_wrong_rank_output(self):
        self.candidate()
        self.plant(TESTS[0], 'rank0/recv_src_idx', lambda b: bytes([b[0] ^ 1]) + b[1:])
        results = judge_variant.compare_recorded(self.bundle)
        self.assertEqual([r['verdict'] for r in results], ['different', 'equal'])
        self.assertTrue(any(d.get('recorded_sha256') for d in results[0]['differences']))

    def test_planted_wrong_sum_is_flagged(self):
        # A combine that adds a token once per rank it was sent to, whatever the ranks returned: right for the
        # factors (1, 1), wrong for (1, -0.5).
        identity, weighted = TESTS
        self.plant(weighted, 'rank1/combined_x', lambda data: judge.references(identity)[1]['combined_x'].data)
        self.assertEqual(self.verdicts(), {'intranode/identity': 'equal', 'intranode/rank_weighted': 'different'})
        (entry,) = [entry for entry in judge.judge(BATCH, self.bundle) if entry['differences']]
        (difference,) = entry['differences']
        self.assertEqual((difference['output'], difference['repeats']), ('rank1/combined_x', 2))
        self.assertGreater(difference['gate'], 0)
        self.assertIn('rank1/combined_x: repeats 2', judge.render([entry]))

    def test_one_wrong_bit_one_extra_row_and_one_odd_repeat_are_flagged(self):
        identity, weighted = TESTS
        flip = lambda data: bytes([data[0] ^ 1]) + data[1:]
        self.plant(identity, 'rank0/recv_topk_weights', flip)  # within every tolerance, still not the reference
        self.plant(weighted, 'rank0/recv_src_idx', lambda data: data[:-4] + bytes(4), repeats=1)  # a row too many, once
        results = {entry['test']: entry for entry in judge.judge(BATCH, self.bundle)}
        self.assertEqual({test: entry['verdict'] for test, entry in results.items()},
                         {'intranode/identity': 'different', 'intranode/rank_weighted': 'different'})
        (bit,), (row,) = results['intranode/identity']['differences'], results['intranode/rank_weighted']['differences']
        self.assertEqual((bit['gate'], bit['max_ulp']), (0, 1))
        self.assertEqual((row['footprint'], row['repeats']), (1, 1))

    def test_missing_output_and_failed_test_are_not_equal(self):
        identity, weighted = TESTS
        self.edit(identity['id'] + '/meta.json', lambda meta: meta['distinct'].pop('rank1/combined_x'))
        self.edit('manifest.json', lambda manifest: manifest['tests'].update({weighted['id']: 'timeout'}))
        self.assertEqual(self.verdicts(), {'intranode/identity': 'different', 'intranode/rank_weighted': 'not judged'})


class Harness(unittest.TestCase):
    def test_calls_the_port_in_the_order_of_its_test(self):
        torch, port, utils = mock.MagicMock(), mock.MagicMock(), mock.MagicMock()
        group = mock.MagicMock(**{'rank.return_value': 1, 'size.return_value': 2})
        buffer = port.EPBuffer.return_value
        per_rank, per_expert, in_rank, recv_x, recv_idx, recv_weights, src_idx, combined_x, combined_weights = (
            mock.MagicMock() for _ in range(9))
        handle = ('rank_prefix', 'channel_prefix', 'recv_channel_prefix', src_idx, in_rank, 'send_head')
        buffer.get_dispatch_layout.return_value = (per_rank, per_expert, in_rank)
        buffer.dispatch.return_value = (recv_x, recv_idx, recv_weights, [], handle)
        buffer.combine.return_value = (combined_x, combined_weights)

        def init_dist(local_rank, num_local_ranks):
            # The pinned init_dist multiplies WORLD_SIZE by its second argument.
            self.assertFalse({'RANK', 'WORLD_SIZE'} & set(os.environ))
            return local_rank, num_local_ranks, group

        utils.init_dist.side_effect = init_dist
        modules = {'torch': torch, 'buffer': port, 'tilelang': mock.MagicMock(),
                   'tilelang.distributed': mock.MagicMock(), 'tilelang.distributed.utils': utils}
        inputs = {name: mock.MagicMock() for name in ('x', 'topk_idx', 'topk_weights')}
        x, topk_idx, topk_weights = (inputs[name].__getitem__.return_value.clone.return_value
                                     for name in ('x', 'topk_idx', 'topk_weights'))
        outputs = mock.MagicMock()
        test = TESTS[1]
        with mock.patch.dict(sys.modules, modules), mock.patch.dict(os.environ, {'RANK': '1', 'WORLD_SIZE': '2'}), \
                mock.patch.object(sys, 'path', list(sys.path)), contextlib.redirect_stdout(io.StringIO()) as log, \
                mock.patch('gpurun.dist.deepep_port', return_value=Path('/checkout/port')):
            run.load_entry(test['entry'], ROOT)(1, 2, inputs, outputs, test['launch'])
            self.assertEqual(sys.path[0], '/checkout/port')
            self.assertEqual((os.environ['RANK'], os.environ['WORLD_SIZE']), ('1', '2'))  # gpurun reads RANK afterwards
        for tensor in inputs.values():
            tensor.__getitem__.assert_called_once_with(1)  # this rank's slice
        port.EPBuffer.assert_called_once_with(group, 2**30, topk_idx.shape[1], 8, x.shape[1])
        recv_x.__mul__.assert_called_once_with(-0.5)  # rank 1 of the factors (1, -0.5)
        self.assertEqual(buffer.mock_calls, [
            mock.call.get_dispatch_layout(topk_idx),
            mock.call.dispatch(x, None, per_rank, in_rank, per_expert, topk_idx, topk_weights, 1),
            mock.call.combine(recv_x.__mul__.return_value, handle, recv_weights)])
        kept = dict(zip([call.args[0] for call in outputs.__getitem__.call_args_list],
                        [call.args[0] for call in outputs.__getitem__.return_value.__getitem__.return_value.copy_.call_args_list]))
        self.assertEqual(kept, {
            'num_tokens_per_rank': per_rank, 'num_tokens_per_expert': per_expert, 'is_token_in_rank': in_rank,
            'recv_x': recv_x, 'recv_src_idx': src_idx, 'recv_topk_idx': recv_idx, 'recv_topk_weights': recv_weights,
            'combined_x': combined_x, 'combined_topk_weights': combined_weights})
        self.assertEqual(group.barrier.call_count, 3)
        self.assertEqual([line.split()[2].strip("{':") for line in log.getvalue().splitlines()],
                         ['num_tokens_per_rank', 'layout', 'recv_x', 'combined_x'])  # one line per step reached
        torch.distributed.destroy_process_group.assert_called_once_with()


if __name__ == '__main__':
    unittest.main()
