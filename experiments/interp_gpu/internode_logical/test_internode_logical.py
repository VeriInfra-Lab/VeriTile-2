#!/usr/bin/env python3
"""Self-test of the logical-node tutorial requests: the judge, the batches and the harness's calls. No GPU, torch or triton_dist needed.

    python3 -B -m unittest discover -s experiments/interp_gpu/internode_logical -p 'test_*.py'
"""
import contextlib
import inspect
import io
import json
import os
from pathlib import Path
import shutil
import struct
import sys
import tempfile
import unittest
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parent))
import harness
import judge
from judge import ROOT
from gpurun import dist, env as environment, run
from interp import gen_inputs, tensorfile
from interp.tensorfile import Tensor

AG03, RS06 = 'internode-logical-ag03-001', 'internode-logical-rs06-001'
AG03_2X2, RS06_2X2 = 'internode-logical-ag03-2x2-001', 'internode-logical-rs06-2x2-001'  # 2 logical nodes of 2 ranks
RS06_NVSHMEM = 'internode-logical-rs06-2x2-002'
RANKS = {AG03: 2, RS06: 2, AG03_2X2: 4, RS06_2X2: 4, RS06_NVSHMEM: 4}
TESTS = {name: json.loads((judge.BATCHES / name / 'batch.json').read_text())['tests'] for name in RANKS}
ONE_NODE = {'ranks': 2, 'launcher': 'triton-dist'}
TWO_NODES = {'ranks': 2, 'launcher': judge.LOGICAL, 'logical_nodes': 2}
ONE_OF_FOUR, TWO_BY_TWO = {**ONE_NODE, 'ranks': 4}, {**TWO_NODES, 'ranks': 4}


class Expected(unittest.TestCase):
    def test_all_gather_is_the_segments_in_rank_order(self):
        self.assertEqual(judge.all_gather([[1, 2], [3, 4], [5, 6]]), [1, 2, 3, 4, 5, 6])

    def test_reduce_scatter_by_hand(self):
        x = [[[1, 2], [3, 4], [5, 6], [7, 8]], [[10, 20], [30, 40], [50, 60], [70, -8]]]
        self.assertEqual(judge.reduce_scatter(x), [[[11, 22], [33, 44]], [[55, 66], [77, 0]]])

    def test_topology_is_what_the_environment_batch_returned(self):
        # The decoded values of `internode-logical-env-002`, recorded on issue #353.
        self.assertEqual([judge.topology(ONE_NODE, rank) for rank in (0, 1)], [[0, 2, 2, 1, 0, 0], [1, 2, 2, 1, 1, 1]])
        self.assertEqual([judge.topology(TWO_NODES, rank) for rank in (0, 1)], [[0, 2, 1, 2, 0, 0], [1, 2, 1, 2, 0, 0]])

    def test_four_ranks_by_hand(self):
        x = [[[1], [2], [3], [4]], [[10], [20], [30], [40]], [[100], [200], [-100], [-200]], [[5], [5], [5], [5]]]
        self.assertEqual(judge.reduce_scatter(x), [[[116]], [[227]], [[-62]], [[-151]]])
        # As gpurun's own test of the launcher has them (scripts/gpurun/test_dist.py): a node sees only its own GPUs.
        self.assertEqual([judge.topology(ONE_OF_FOUR, rank) for rank in range(4)],
                         [[0, 4, 4, 1, 0, 0], [1, 4, 4, 1, 1, 1], [2, 4, 4, 1, 2, 2], [3, 4, 4, 1, 3, 3]])
        self.assertEqual([judge.topology(TWO_BY_TWO, rank) for rank in range(4)],
                         [[0, 4, 2, 2, 0, 0], [1, 4, 2, 2, 1, 1], [2, 4, 2, 2, 0, 0], [3, 4, 2, 2, 1, 1]])

    def test_a_sum_bfloat16_cannot_hold_is_refused(self):
        self.assertEqual(judge.encode('bf16', -200), bytes.fromhex('48c3'))
        self.assertEqual(judge.encode('bf16', -256), bytes.fromhex('80c3'))  # four inputs of magnitude 64
        with self.assertRaisesRegex(ValueError, 'not exact in bf16'):
            judge.encode('bf16', 257)  # nine significant bits: the reference would need a rounding rule


class Batches(unittest.TestCase):
    def test_gpurun_loads_them_and_the_inputs_are_the_pinned_ones(self):
        for name, tests in TESTS.items():
            batch = run.load_batch(judge.BATCHES / name)
            self.assertEqual((batch['batch_id'], batch['mode'], batch['requires']),
                             (name, 'dist', {'sm': 90, 'gpus': RANKS[name], 'env': 'triton-dist'}))
            for test in tests:
                path, _, function = test['entry'].partition('::')
                self.assertEqual(ROOT / path, Path(harness.__file__).resolve())
                self.assertTrue(callable(getattr(harness, function)))
                for spec in test['inputs']:
                    self.assertEqual(gen_inputs.generate(spec['dtype'], spec['shape'], spec['gen']).sha256(), spec['sha256'])

    def test_barrier_reports_for_original_and_replacement_batches(self):
        for name in (RS06, RS06_2X2, RS06_NVSHMEM):
            test = TESTS[name][0]
            ranks = test['ranks']
            spec = dict(test['inputs'][0], shape=[ranks, ranks, 1])
            barrier_output, = [out for out in test['outputs'] if out['name'] == 'barrier']
            for rank, outputs in judge.references(dict(test, inputs=[spec], outputs=[barrier_output])).items():
                with self.subTest(batch=name, rank=rank):
                    expected = (-1, -1, 2) if name == RS06_NVSHMEM else (rank, ranks, 1)
                    self.assertEqual(struct.unpack('<iii', outputs['barrier'].data), expected)
        self.assertEqual(run.load_batch(judge.BATCHES / RS06_NVSHMEM)['supersedes'], RS06_2X2)

    def test_every_logical_node_test_has_its_control(self):
        for name, tests in TESTS.items():
            sides = {}
            for test in tests:
                side, _, what = test['id'].partition('/')
                self.assertEqual({key: test.get(key) for key in TWO_NODES},
                                 {'one_node': {**ONE_NODE, 'ranks': RANKS[name], 'logical_nodes': None},
                                  'logical_nodes': {**TWO_NODES, 'ranks': RANKS[name]}}[side])
                sides.setdefault(side, {})[what] = {key: test[key] for key in ('entry', 'launch', 'inputs', 'outputs')}
            self.assertEqual(sides['one_node'], sides['logical_nodes'])
        for name in (AG03, AG03_2X2):
            self.assertEqual([test['launch'] for test in TESTS[name][:2]], [{'kernel': 'push_1d'}, {'kernel': 'push_2d'}])

    def test_shapes_stay_where_the_tutorials_are_read(self):
        for test in TESTS[AG03] + TESTS[AG03_2X2]:
            (given,), gathered = test['inputs'], test['outputs'][1]
            self.assertEqual((given['shape'], given['shape'][0] % test['ranks']), (gathered['shape'], 0))
        for test in TESTS[RS06] + TESTS[RS06_2X2] + TESTS[RS06_NVSHMEM]:
            (given,), reduced = test['inputs'], test['outputs'][2]
            ranks, M, N = given['shape']
            self.assertEqual((ranks, reduced['shape']), (test['ranks'], [M // ranks, N]))
            # Every tile of `kernel_ring_reduce_tma` (256 rows by 64 or 128 columns) lies inside its tensors, as with
            # the tutorial's own 8192 by 16384: the request does not depend on how a tile behaves across a border.
            self.assertEqual(((M // ranks) % 256, N % 128), (0, 0))
            # The sum of any of the inputs is an integer bfloat16 holds exactly (8 significant bits, or 256).
            bound = max(abs(given['gen'].get('low', -100)), abs(given['gen'].get('high', 100)))
            self.assertLessEqual(ranks * bound, 256)

    def test_gpurun_runs_the_four_rank_tests_on_four_gpus_and_not_on_two(self):
        def h800(count):
            return {'gpus': [{'name': 'H800', 'sm': 90}] * count, 'versions': {'triton_dist': '3.7.1+git7908e4ea'}}
        with mock.patch.object(dist, 'launch_script', return_value=Path('/td/scripts/launch.sh')):
            for name in (AG03_2X2, RS06_2X2, RS06_NVSHMEM):
                batch = run.load_batch(judge.BATCHES / name)
                with mock.patch.dict(os.environ, {'CUDA_VISIBLE_DEVICES': '2,3,4,5'}):  # pair, pair
                    self.assertEqual(environment.mismatches(batch['requires'], h800(4)), [])
                    self.assertEqual([dist.refusals(test, h800(4), 1) for test in batch['tests']], [[]] * len(batch['tests']))
                    script = dist.logical_nodes(batch['tests'][-1], Path('/work'))[2]
                    for node, pair in enumerate(('2,3', '4,5')):  # each logical node holds one pair
                        self.assertIn(f'CUDA_VISIBLE_DEVICES={pair} ARNOLD_WORKER_NUM=2 ARNOLD_ID={node} ', script)
                with mock.patch.dict(os.environ, {'CUDA_VISIBLE_DEVICES': '4,5'}):
                    self.assertEqual(environment.mismatches(batch['requires'], h800(2)),
                                     ["needs 4 GPU(s) with sm_90; found [90, 90]"])
                    for test in batch['tests']:
                        self.assertIn('needs 4 GPUs, one per rank; 2 visible', dist.refusals(test, h800(2), 1))

    def test_the_one_predicted_failure_is_last_and_bounded(self):
        self.assertFalse(any(judge.predicted_failure(test) for name in (AG03, AG03_2X2, RS06_2X2) for test in TESTS[name]))
        # With four ranks only the context built by the harness; either test may hang in the tutorial's barrier.
        self.assertEqual([(test['launch'], test['timeout_s']) for test in TESTS[RS06_2X2]], [({'context': 'harness'}, 300)] * 2)
        *others, last = TESTS[RS06]
        self.assertEqual([judge.predicted_failure(test) for test in TESTS[RS06]], [False, False, False, True])
        self.assertEqual((last['id'], last['timeout_s'], last['repeats']), ('logical_nodes/tutorial_context', 240, 1))
        self.assertFalse(any('timeout_s' in test for test in others))


# What a rank of a correct run returns, as an entry of gpurun's CPU mock; the predicted failure fails as predicted.
ENTRY = '''
import json, sys
sys.path.insert(0, {here!r})
import judge

def run(rank, ranks, inputs, outputs, launch):
    batch, name = launch['of']
    test, = [test for test in json.loads((judge.BATCHES / batch / 'batch.json').read_text())['tests'] if test['id'] == name]
    if judge.predicted_failure(test) and rank >= ranks // test['logical_nodes']:
        raise IndexError('list index out of range')
    outputs.update(judge.references(test)[rank])
'''


class Judge(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        """The bundles gpurun itself writes for the two batches when every rank returns the reference."""
        temp = tempfile.TemporaryDirectory()
        cls.addClassCleanup(temp.cleanup)
        cls.written = Path(temp.name)
        (cls.written / 'entry.py').write_text(ENTRY.format(here=str(Path(__file__).resolve().parent)))
        for name in TESTS:
            batch = json.loads((judge.BATCHES / name / 'batch.json').read_text())
            batch['requires'] = {}
            for test in batch['tests']:
                test.update(frontend='mock', launcher='mock', entry='entry.py::run', launch={'of': [name, test['id']]})
                test.pop('logical_nodes', None)  # the mock launcher has no nodes
            (cls.written / name).mkdir()
            (cls.written / name / 'batch.json').write_text(json.dumps(batch))
            run.run_batch(cls.written / name, cls.written / 'bundles' / name, env={'gpus': [], 'versions': {}},
                          root=cls.written)

    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.bundles = shutil.copytree(self.written / 'bundles', Path(temp.name) / 'bundles')

    def edit(self, batch, name, change):
        text = json.loads((self.bundles / batch / name).read_text())
        change(text)
        (self.bundles / batch / name).write_text(json.dumps(text))

    def plant(self, batch, test, key, change):
        """Replace the stored value of one output by `change(reference bytes)` in both repeats."""
        (sha256,) = json.loads((self.bundles / batch / test / 'meta.json').read_text())['distinct'][key]
        right = tensorfile.read(self.bundles / batch / test / 'out' / key / (sha256 + '.tensor'))
        wrong = Tensor(right.dtype, right.shape, change(right.data))
        tensorfile.write(self.bundles / batch / test / 'out' / key / (wrong.sha256() + '.tensor'), wrong)
        self.edit(batch, test + '/meta.json', lambda meta: meta['distinct'].update({key: {wrong.sha256(): 2}}))

    def judged(self, batch):
        return {entry['test']: entry for entry in judge.judge(judge.BATCHES / batch, self.bundles / batch)}

    def verdicts(self, batch):
        return {test: entry['verdict'] for test, entry in self.judged(batch).items()}

    def different(self, batch, test):
        """The outputs of a test that differ, with their differences."""
        return {key: found for key, found in self.judged(batch)[test]['outputs'].items() if found}

    def test_nvshmem_batch_rejects_a_rank_reporting_the_cas_barrier(self):
        name = 'logical_nodes/harness_context'
        self.assertEqual(self.verdicts(RS06_NVSHMEM)[name], 'equal')
        self.plant(RS06_NVSHMEM, name, 'rank3/barrier',
                   lambda _: b''.join(judge.encode('int32', n) for n in (3, 4, 1)))
        result = self.judged(RS06_NVSHMEM)[name]
        self.assertEqual(result['verdict'], 'different')
        self.assertEqual({key for key, diff in result['outputs'].items() if diff}, {'rank3/barrier'})

    def test_reference_bundles_are_equal_and_the_predicted_failure_is_seen(self):
        for name in (AG03, AG03_2X2, RS06_2X2, RS06_NVSHMEM):
            self.assertEqual(self.verdicts(name), {test['id']: 'equal' for test in TESTS[name]})
        self.assertEqual(sorted(self.judged(RS06_2X2)['logical_nodes/harness_context']['outputs']),
                         sorted(f'rank{rank}/{name}' for rank in range(4) for name in ('topology', 'barrier', 'reduced')))
        self.assertEqual(self.verdicts(RS06), {
            'one_node/tutorial_context': 'equal', 'one_node/harness_context': 'equal',
            'logical_nodes/harness_context': 'equal', 'logical_nodes/tutorial_context': 'failed as predicted'})
        entry = self.judged(RS06)['logical_nodes/harness_context']
        self.assertEqual(entry['outputs'], {f'rank{rank}/{name}': [] for rank in (0, 1)
                                            for name in ('topology', 'barrier', 'reduced')})
        text = judge.render(self.judged(RS06).values())
        self.assertIn('  rank1/reduced: equal\n', text)
        self.assertIn("logical_nodes/tutorial_context: failed as predicted (GPU status runtime_error, "
                      "rank status ['ok', 'runtime_error'])", text)

    def test_planted_all_gather_without_the_peers_segment_is_flagged(self):
        # Rank 0 after a kernel whose peer never sent: its own 32 bytes, the sentinel in segment 1.
        self.plant(AG03, 'logical_nodes/push_2d', 'rank0/gathered', lambda data: data[:32] + b'\x80' * 32)
        self.assertEqual(self.verdicts(AG03), {**{test['id']: 'equal' for test in TESTS[AG03]},
                                               'logical_nodes/push_2d': 'different'})
        (key, (found,)), = self.different(AG03, 'logical_nodes/push_2d').items()
        self.assertEqual((key, found['repeats'], found['footprint'], found['exact']), ('rank0/gathered', 2, 32, 0))
        self.assertIn('  rank0/gathered: repeats 2, footprint 32,', judge.render(self.judged(AG03).values()))

    def test_planted_all_gather_with_segments_exchanged_is_flagged(self):
        self.plant(AG03, 'one_node/push_1d', 'rank1/gathered', lambda data: data[32:] + data[:32])
        (key, (found,)), = self.different(AG03, 'one_node/push_1d').items()
        self.assertEqual((key, found['footprint']), ('rank1/gathered', 0))
        self.assertGreater(found['exact'], 0)

    def test_planted_forward_of_a_segment_not_yet_received_is_flagged(self):
        # Two nodes of two, rank 1: segment 2 comes from rank 2 through rank 0, which must wait for it (`T03:160-167`)
        # before it forwards. Forwarded too early, rank 1 holds the sentinel there, with its signal set all the same.
        self.plant(AG03_2X2, 'logical_nodes/push_2d', 'rank1/gathered', lambda data: data[:32] + b'\x80' * 16 + data[48:])
        self.assertEqual(self.verdicts(AG03_2X2), {**{test['id']: 'equal' for test in TESTS[AG03_2X2]},
                                                   'logical_nodes/push_2d': 'different'})
        (key, (found,)), = self.different(AG03_2X2, 'logical_nodes/push_2d').items()
        self.assertEqual((key, found['footprint'], found['segments']), ('rank1/gathered', 16, [2]))
        self.assertIn('footprint 16,', judge.render(self.judged(AG03_2X2).values()))
        self.assertIn('segments [2]', judge.render(self.judged(AG03_2X2).values()))

    def test_planted_all_gather_of_four_with_two_segments_exchanged_is_flagged(self):
        self.plant(AG03_2X2, 'one_node/push_1d', 'rank3/gathered', lambda data: data[16:32] + data[:16] + data[32:])
        (key, (found,)), = self.different(AG03_2X2, 'one_node/push_1d').items()
        self.assertEqual((key, found['footprint'], found['segments']), ('rank3/gathered', 0, [0, 1]))

    def test_planted_reduce_scatter_of_four_without_a_local_rank_or_without_the_other_node_is_flagged(self):
        test = TESTS[RS06_2X2][1]
        spec, = test['inputs']
        x = judge.nested(gen_inputs.generate(spec['dtype'], spec['shape'], spec['gen']))

        def rows(rank, senders):  # the rows of `rank` summed over `senders` only
            return b''.join(judge.encode('bf16', sum(x[sender][row][column] for sender in senders))
                            for row in range(256 * rank, 256 * rank + 256) for column in range(128))
        self.assertEqual(rows(0, range(4)), judge.references(test)[0]['reduced'].data)
        # Rank 0 without what rank 1, the other rank of its node, scattered to it; rank 3 with the sum of its own node
        # only, as when the put of node 0 never landed in its P2P buffer.
        self.plant(RS06_2X2, test['id'], 'rank0/reduced', lambda data: rows(0, (0, 2, 3)))
        self.plant(RS06_2X2, test['id'], 'rank3/reduced', lambda data: rows(3, (2, 3)))
        self.assertEqual(self.verdicts(RS06_2X2), {'one_node/harness_context': 'equal', test['id']: 'different'})
        different = self.different(RS06_2X2, test['id'])
        self.assertEqual(sorted(different), ['rank0/reduced', 'rank3/reduced'])
        for (found,) in different.values():
            self.assertEqual(found['footprint'], 0)
            self.assertGreater(found['gate'], 0)

    def test_two_nodes_of_two_that_came_up_as_one_node_of_four_are_flagged(self):
        one_node = judge.references(TESTS[AG03_2X2][1])
        for rank in range(4):
            self.plant(AG03_2X2, 'logical_nodes/push_2d', f'rank{rank}/topology',
                       lambda data, rank=rank: one_node[rank]['topology'].data)
        # Ranks 0 and 1 have the same LOCAL_RANK and device under both; LOCAL_WORLD_SIZE and the node count differ.
        self.assertEqual(set(self.different(AG03_2X2, 'logical_nodes/push_2d')), {f'rank{rank}/topology' for rank in range(4)})

    def test_a_first_pair_without_native_atomics_or_a_node_team_of_one_pair_is_flagged(self):
        self.plant(RS06_2X2, 'one_node/harness_context', 'rank2/barrier', lambda data: data[:8] + bytes(4))
        self.plant(RS06_2X2, 'logical_nodes/harness_context', 'rank2/barrier',
                   lambda data: (0).to_bytes(4, 'little') + (2).to_bytes(4, 'little') + data[8:])
        for test in TESTS[RS06_2X2]:
            self.assertEqual(set(self.different(RS06_2X2, test['id'])), {'rank2/barrier'})

    def test_planted_reduce_scatter_that_did_not_add_the_peer_is_flagged(self):
        # Rank 1 returns its own rows of its own input: the sum without what rank 0 sent across the nodes.
        spec, = TESTS[RS06][2]['inputs']
        own = judge.nested(gen_inputs.generate(spec['dtype'], spec['shape'], spec['gen']))[1][256:]
        unreduced = b''.join(judge.encode('bf16', value) for value in judge.flat(own))
        self.plant(RS06, 'logical_nodes/harness_context', 'rank1/reduced', lambda data: unreduced)
        self.assertEqual(self.verdicts(RS06)['logical_nodes/harness_context'], 'different')
        (key, (found,)), = self.different(RS06, 'logical_nodes/harness_context').items()
        self.assertEqual((key, found['footprint']), ('rank1/reduced', 0))
        self.assertGreater(found['gate'], 0)

    def test_one_wrong_bit_of_a_sum_is_flagged(self):
        self.plant(RS06, 'one_node/tutorial_context', 'rank0/reduced', lambda data: bytes([data[0] ^ 1]) + data[1:])
        (key, (found,)), = self.different(RS06, 'one_node/tutorial_context').items()
        self.assertEqual((key, found['gate'], found['max_ulp']), ('rank0/reduced', 0, 1))  # inside every tolerance

    def test_logical_nodes_that_came_up_as_one_node_are_flagged(self):
        one_node = judge.references(TESTS[RS06][1])
        for rank in (0, 1):
            self.plant(RS06, 'logical_nodes/harness_context', f'rank{rank}/topology',
                       lambda data, rank=rank: one_node[rank]['topology'].data)
        self.assertEqual(set(self.different(RS06, 'logical_nodes/harness_context')), {'rank0/topology', 'rank1/topology'})

    def test_a_pair_without_native_atomics_is_flagged(self):
        self.plant(RS06, 'one_node/harness_context', 'rank0/barrier', lambda data: data[:8] + bytes(4))
        self.assertEqual(set(self.different(RS06, 'one_node/harness_context')), {'rank0/barrier'})

    def test_predicted_failure_that_did_not_happen_or_failed_otherwise_is_not_met(self):
        last = 'logical_nodes/tutorial_context'
        (self.bundles / RS06 / last / 'stderr.log').write_text('RuntimeError: CUDA error\n')
        self.assertEqual(self.verdicts(RS06)[last], 'prediction not met')
        self.edit(RS06, 'manifest.json', lambda manifest: manifest['tests'].update({last: 'ok'}))
        self.assertEqual(self.verdicts(RS06)[last], 'prediction not met')

    def test_predicted_failure_with_rank_0_killed_at_the_timeout_is_met(self):
        last = 'logical_nodes/tutorial_context'
        self.edit(RS06, 'manifest.json', lambda manifest: manifest['tests'].update({last: 'timeout'}))
        self.edit(RS06, last + '/meta.json', lambda meta: meta['runs'][0].update(rank_status=[None, 'runtime_error']))
        self.assertEqual(self.verdicts(RS06)[last], 'failed as predicted')
        self.edit(RS06, last + '/meta.json', lambda meta: meta['runs'][0].update(rank_status=['runtime_error', None]))
        self.assertEqual(self.verdicts(RS06)[last], 'prediction not met')  # the rank on node 1 must be the one that raised

    def test_missing_output_and_failed_test_are_not_equal(self):
        self.edit(AG03, 'one_node/push_2d/meta.json', lambda meta: meta['distinct'].pop('rank1/gathered'))
        self.edit(AG03, 'manifest.json', lambda manifest: manifest['tests'].update({'logical_nodes/push_1d': 'timeout'}))
        self.assertEqual(self.verdicts(AG03), {'one_node/push_1d': 'equal', 'one_node/push_2d': 'different',
                                               'logical_nodes/push_1d': 'not judged', 'logical_nodes/push_2d': 'equal'})


# A file shaped like tutorial 03: definitions, then a program with no `__main__` guard.
PROGRAM_AT_IMPORT = '''"""Tutorial."""
import os
from dataclasses import dataclass


def jit(function):
    return function


@dataclass
class Context:
    rank: int
    signal_value: int = 15


@jit
def kernel(a, b):
    return a + b  # the kernel text


RANK = os.environ.setdefault('TUTORIAL_PROGRAM_RAN', '1')
raise SystemExit('the program of the tutorial ran ✅')
'''


class Loaders(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.path = Path(temp.name) / '03-program-at-import.py'
        names = set(sys.modules)
        self.addCleanup(lambda: [sys.modules.pop(name) for name in set(sys.modules) - names])

    def test_definitions_runs_no_program_and_keeps_the_source_text(self):
        self.path.write_text(PROGRAM_AT_IMPORT, encoding='utf-8')
        module = harness.definitions(self.path)
        self.assertNotIn('TUTORIAL_PROGRAM_RAN', os.environ)
        self.assertEqual(sorted(name for name in vars(module) if not name.startswith('__')),
                         ['Context', 'dataclass', 'jit', 'kernel', 'os'])
        self.assertEqual((module.kernel(1, 2), module.Context(rank=1).signal_value), (3, 15))
        # What Triton's JIT reads: the text of the file, at its lines.
        self.assertEqual(inspect.getsourcelines(module.kernel),
                         (['@jit\n', 'def kernel(a, b):\n', '    return a + b  # the kernel text\n'], 16))
        self.assertEqual(module.kernel.__code__.co_filename, str(self.path))

    def test_imported_runs_what_import_runs(self):
        self.path.write_text(PROGRAM_AT_IMPORT.replace("raise SystemExit", "if __name__ == '__main__':\n    raise SystemExit"),
                             encoding='utf-8')
        with mock.patch.dict(os.environ):
            module = harness.imported(self.path)
            self.assertEqual((module.RANK, module.kernel(1, 2)), ('1', 3))


class Harness(unittest.TestCase):
    """Every line of the harnesses runs here against stand-ins; what the pinned code does with the calls is not tested."""

    def call(self, function, launch, inputs, tutorial, rank=1, ranks=2, local=1, actual_barrier=None):
        """As rank `rank` of `ranks` on logical nodes of `local` ranks; by default rank 1 of two nodes of one."""
        torch, utils, common_ops = mock.MagicMock(), mock.MagicMock(), mock.MagicMock()
        group = utils.initialize_distributed.return_value
        group.rank.return_value, group.size.return_value = rank, ranks
        # One tensor per rank of the node, and a logical node sees one device per rank.
        utils.nvshmem_create_tensors.side_effect = lambda *args: [mock.MagicMock() for _ in range(local)]
        torch.cuda.device_count.return_value = local
        utils.cudart.cudaDeviceGetP2PAttribute.return_value = (0, 1)
        modules = {'torch': torch, 'triton_dist': mock.MagicMock(), 'triton_dist.utils': utils,
                   'triton_dist.kernels': mock.MagicMock(), 'triton_dist.kernels.nvidia': mock.MagicMock(),
                   'triton_dist.kernels.nvidia.common_ops': common_ops}
        def make_barrier(is_intra_node):
            barrier = mock.Mock(spec=['is_intra_node', 'finalize'] +
                                (['local_rank', 'num_local_ranks'] if is_intra_node else []))
            barrier.is_intra_node = is_intra_node
            common_ops.BarrierAllContext.return_value = barrier
            return barrier
        common_ops.BarrierAllContext.side_effect = make_barrier
        def make_context(**fields):
            context = tutorial.ReduceScatter2DContext.return_value
            context.barrier = actual_barrier if actual_barrier is not None else fields['barrier']
            return context
        tutorial.ReduceScatter2DContext.side_effect = make_context
        outputs = mock.MagicMock()
        variables = {'RANK': str(rank), 'WORLD_SIZE': str(ranks), 'LOCAL_WORLD_SIZE': str(local),
                     'LOCAL_RANK': str(rank % local)}
        self.printed = io.StringIO()
        with mock.patch.dict(sys.modules, modules), mock.patch.dict(os.environ, variables), \
                contextlib.redirect_stdout(self.printed), \
                mock.patch.object(harness, 'tutorial_file', lambda name: Path('/checkout/tutorials') / name), \
                mock.patch.object(harness, 'definitions', return_value=tutorial) as definitions, \
                mock.patch.object(harness, 'imported', return_value=tutorial) as imported:
            function(rank, ranks, inputs, outputs, launch)
        return torch, utils, common_ops, outputs, definitions, imported

    def test_all_gather_calls_the_chosen_kernel_of_tutorial_03(self):
        tutorial, x = mock.MagicMock(), mock.MagicMock()
        x.numel.return_value = 64
        torch, utils, _, outputs, definitions, imported = self.call(
            harness.all_gather, TESTS[AG03][3]['launch'], {'x': x}, tutorial)
        definitions.assert_called_once_with(Path('/checkout/tutorials/03-inter-node-allgather.py'))
        imported.assert_not_called()  # importing tutorial 03 would run its program
        buffer = utils.nvshmem_create_tensor.return_value
        self.assertEqual(utils.nvshmem_create_tensor.call_args_list, [
            mock.call((64, ), torch.int8), *[mock.call((2, ), utils.NVSHMEM_SIGNAL_DTYPE)] * 2])  # a signal word per rank
        buffer.__getitem__.assert_called_once_with(slice(32, 64))  # rank 1 writes segment 1 only
        tutorial.AllGatherContext.assert_called_once_with(rank=1, node=1, num_ranks=2, num_nodes=2,
                                                          symm_signals=[buffer, buffer], signal_value=10)
        tutorial.all_gather_push_2d.assert_called_once_with(tutorial.AllGatherContext.return_value, buffer)
        tutorial.all_gather_push_1d.assert_not_called()
        self.assertEqual(utils.nvshmem_barrier_all_on_stream.call_count, 2)
        self.assertEqual(utils.nvshmem_free_tensor_sync.call_count, 3)
        utils.finalize_distributed.assert_called_once_with()
        self.assertEqual([call.args[0] for call in outputs.__getitem__.call_args_list],
                         ['topology', 'gathered', 'gathered'])

    def test_all_gather_as_a_rank_of_two_nodes_of_two(self):
        tutorial, x = mock.MagicMock(), mock.MagicMock()
        x.numel.return_value = 64
        torch, utils, *_ = self.call(harness.all_gather, TESTS[AG03_2X2][3]['launch'], {'x': x}, tutorial,
                                     rank=3, ranks=4, local=2)
        buffer = utils.nvshmem_create_tensor.return_value
        self.assertEqual(utils.nvshmem_create_tensor.call_args_list, [
            mock.call((64, ), torch.int8), *[mock.call((4, ), utils.NVSHMEM_SIGNAL_DTYPE)] * 2])  # words 0 to 3 are addressed
        buffer.__getitem__.assert_called_once_with(slice(48, 64))
        tutorial.AllGatherContext.assert_called_once_with(rank=3, node=1, num_ranks=4, num_nodes=2,
                                                          symm_signals=[buffer, buffer], signal_value=10)
        tutorial.all_gather_push_2d.assert_called_once_with(tutorial.AllGatherContext.return_value, buffer)

    def reduce_scatter(self, launch, shape=(512, 128), **where):
        tutorial, given = mock.MagicMock(), mock.MagicMock()
        x = given.__getitem__.return_value.to.return_value
        x.shape = shape
        torch, utils, common_ops, outputs, definitions, imported = self.call(
            harness.reduce_scatter, launch, {'x': given}, tutorial, **where)
        imported.assert_called_once_with(Path('/checkout/tutorials/06-inter-node-reduce-scatter.py'))
        definitions.assert_not_called()
        given.__getitem__.assert_called_once_with(where.get('rank', 1))  # this rank's matrix
        given.__getitem__.return_value.to.assert_called_once_with(torch.bfloat16)
        self.assertEqual([call.args[0] for call in outputs.__getitem__.call_args_list], ['topology', 'barrier', 'reduced'])
        outputs.__getitem__.return_value.copy_.assert_called_with(tutorial.reduce_scatter_2d_op.return_value)
        utils.finalize_distributed.assert_called_once_with()
        return tutorial, x, torch, utils, common_ops

    def test_reduce_scatter_with_the_tutorials_context(self):
        tutorial, x, _, utils, _ = self.reduce_scatter(TESTS[RS06][3]['launch'])
        tutorial.create_reduce_scater_2d_ctx.assert_called_once_with(512, 128, 1, 2, 1, x.dtype, overlap_with_gemm=False)
        tutorial.ReduceScatter2DContext.assert_not_called()
        utils.nvshmem_create_tensors.assert_not_called()
        context = tutorial.create_reduce_scater_2d_ctx.return_value
        tutorial.reduce_scatter_2d_op.assert_called_once_with(x, context)
        context.finalize.assert_called_once_with()

    def test_reduce_scatter_with_the_harness_context(self):
        # The stand-in returns one tensor, as the pinned code does for a node of one rank: `signal[1]`, the
        # tutorial's index for rank 1, would raise here as it is predicted to on the GPU.
        tutorial, x, torch, utils, common_ops = self.reduce_scatter(TESTS[RS06][2]['launch'])
        tutorial.create_reduce_scater_2d_ctx.assert_not_called()
        self.assertEqual(utils.nvshmem_create_tensors.call_args_list, [
            *[mock.call([512, 128], x.dtype, 1, 1)] * 3, mock.call([4], utils.NVSHMEM_SIGNAL_DTYPE, 1, 1)])
        (), fields = tutorial.ReduceScatter2DContext.call_args
        (signal,) = fields['symm_signal_bufs']
        signal.zero_.assert_called_once_with()
        self.assertEqual({name: fields[name] for name in ('max_M', 'N', 'rank', 'world_size', 'local_world_size',
                                                          'dtype', 'overlap_with_gemm', 'barrier', 'num_sync_sms',
                                                          'num_p2p_sms', 'num_reduction_sms')},
                         {'max_M': 512, 'N': 128, 'rank': 1, 'world_size': 2, 'local_world_size': 1, 'dtype': x.dtype,
                          'overlap_with_gemm': False, 'barrier': common_ops.BarrierAllContext.return_value,
                          'num_sync_sms': 0, 'num_p2p_sms': 1, 'num_reduction_sms': 15})
        common_ops.BarrierAllContext.assert_called_once_with(True)
        self.assertEqual(len({id(fields[name]) for name in ('symm_scatter_bufs', 'symm_rs_per_node_bufs',
                                                             'symm_p2p_bufs', 'symm_signal_bufs')}), 4)
        context = tutorial.ReduceScatter2DContext.return_value
        tutorial.reduce_scatter_2d_op.assert_called_once_with(x, context)
        context.finalize.assert_called_once_with()
        context.barrier.finalize.assert_called_once_with()
        utils.cudart.cudaDeviceGetP2PAttribute.assert_not_called()  # one visible device has no pair to ask about
        self.assertIn('rank 1: native atomics between visible devices: one device\n', self.printed.getvalue())

    def test_nvshmem_launch_constructs_a_global_barrier_without_node_team_fields(self):
        for test in TESTS[RS06_NVSHMEM]:
            with self.subTest(test=test['id']):
                _, _, torch, utils, common_ops = self.reduce_scatter(
                    test['launch'], shape=(1024, 128), rank=3, ranks=4, local=4 // test.get('logical_nodes', 1))
                common_ops.BarrierAllContext.assert_called_once_with(False)
                utils.supports_p2p_native_atomic.assert_not_called()
                self.assertIn(mock.call([-1, -1, 2], dtype=torch.int32), torch.tensor.call_args_list)

    def test_report_uses_the_constructed_context_even_if_it_differs_from_launch(self):
        actual = mock.Mock(is_intra_node=True, local_rank=5, num_local_ranks=8)
        _, _, torch, utils, _ = self.reduce_scatter(TESTS[RS06_NVSHMEM][0]['launch'], actual_barrier=actual)
        utils.supports_p2p_native_atomic.assert_called_once_with()
        self.assertIn(mock.call([5, 8, 1], dtype=torch.int32), torch.tensor.call_args_list)

    def test_invalid_barrier_settings_are_rejected_before_launch(self):
        for launch, error in [
            ({'context': 'harness', 'barrier': 'unknown'}, 'unknown barrier'),
            ({'context': 'harness', 'barrier': 'global'}, 'unknown barrier'),
            ({'context': 'harness', 'barrier': 'NVSHMEM'}, 'unknown barrier'),
            ({'context': 'tutorial', 'barrier': 'nvshmem'}, 'tutorial context'),
            ({'context': 'tutorial', 'barrier': 'intra_node'}, 'tutorial context'),
        ]:
            with self.subTest(launch=launch), self.assertRaisesRegex(ValueError, error):
                harness.reduce_scatter(0, 4, {}, {}, launch)

    def test_reduce_scatter_as_a_rank_of_two_nodes_of_two(self):
        tutorial, x, torch, utils, _ = self.reduce_scatter(TESTS[RS06_2X2][1]['launch'], shape=(1024, 128),
                                                           rank=3, ranks=4, local=2)
        # The buffers of `T06:188-201` for a node of two: per-node and P2P buffers of M / 2 rows, 2 * 4 signal words.
        self.assertEqual(utils.nvshmem_create_tensors.call_args_list, [
            mock.call([1024, 128], x.dtype, 3, 2), *[mock.call([512, 128], x.dtype, 3, 2)] * 2,
            mock.call([8], utils.NVSHMEM_SIGNAL_DTYPE, 3, 2)])
        (), fields = tutorial.ReduceScatter2DContext.call_args
        other, own = fields['symm_signal_bufs']  # index 1 within the node; the tutorial's index 3 is past the list
        own.zero_.assert_called_once_with()
        other.zero_.assert_not_called()
        self.assertEqual((fields['rank'], fields['world_size'], fields['local_world_size']), (3, 4, 2))
        # What the pair of visible devices reports, asked as `supports_p2p_native_atomic` asks it.
        native = utils.cudart.cudaDeviceP2PAttr.cudaDevP2PAttrNativeAtomicSupported
        self.assertEqual(utils.cudart.cudaDeviceGetP2PAttribute.call_args_list, [mock.call(native, 0, 1)])
        utils.CUDA_CHECK.assert_called_once_with(0)
        self.assertIn('rank 3: native atomics between visible devices: 0-1:1\n', self.printed.getvalue())


if __name__ == '__main__':
    unittest.main()
