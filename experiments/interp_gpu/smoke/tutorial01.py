"""Run the original producer_consumer_kernel from Triton-distributed 7908e4ea,
tutorials/01-distributed-notify-wait.py. Judge the recorded output on the development host:
PYTHONPATH=scripts python experiments/interp_gpu/smoke/tutorial01.py BUNDLE REQUEST_COMMIT
"""
from hashlib import sha256
import json
from pathlib import Path

BATCH_ID = 'tutorial01-original-smoke-001'
BATCH = Path(__file__).resolve().parents[1] / 'batches' / BATCH_ID
TUTORIAL = '01-distributed-notify-wait.py'
SOURCE_SHA256 = 'e14944ca567312c74923e3fd5750301c3a6914a034f8c3c37d7c742dd384c913'
NUM_INPUTS, QUEUE_SIZE, BLOCK_SIZE = 2025, 32, 128


def pinned_kernel():
    from experiments.interp_gpu.internode_logical.harness import definitions, tutorial_file
    path = tutorial_file(TUTORIAL)
    if sha256(path.read_bytes()).hexdigest() != SOURCE_SHA256:
        raise ValueError('installed tutorial 01 differs from Triton-distributed 7908e4ea')
    # The tutorial runs main unconditionally at import time. Load only its definitions.
    return definitions(path).producer_consumer_kernel


def run(rank, ranks, inputs, outputs, launch):
    import torch
    from triton_dist.utils import (NVSHMEM_SIGNAL_DTYPE, finalize_distributed, initialize_distributed,
                                   nvshmem_barrier_all_on_stream, nvshmem_create_tensor,
                                   nvshmem_free_tensor_sync)

    if ranks != 2:
        raise ValueError('tutorial 01 smoke requires two ranks')
    kernel = pinned_kernel()
    group = initialize_distributed()
    try:
        if (group.rank(), group.size()) != (rank, ranks):
            raise ValueError('runtime rank/world disagrees with the launcher')
        queue = nvshmem_create_tensor((QUEUE_SIZE * BLOCK_SIZE,), torch.float32)
        try:
            signal = nvshmem_create_tensor((QUEUE_SIZE,), NVSHMEM_SIGNAL_DTYPE)
            try:
                queue.fill_(-1)
                signal.fill_(0)
                stream = torch.cuda.current_stream()
                nvshmem_barrier_all_on_stream(stream)
                # Original launch shape, scheduling split, word widths and two GPU-scope waits.
                # Every gpurun repeat starts fresh processes and a fresh queue.
                kernel[(20,)](rank, ranks, inputs[f'send{rank}'], outputs['received'], NUM_INPUTS,
                              queue, signal, QUEUE_SIZE, BLOCK_SIZE, 16, 4, num_warps=4)
                nvshmem_barrier_all_on_stream(stream)
                torch.cuda.synchronize()
            finally:
                nvshmem_free_tensor_sync(signal)
        finally:
            nvshmem_free_tensor_sync(queue)
    finally:
        finalize_distributed()


def judge(batch, bundle, request_commit):
    """Require every rank's previous-rank payload in every repeat, including its raw object."""
    from gpurun import env
    batch, bundle = Path(batch), Path(bundle)
    request = json.loads((batch / 'batch.json').read_text())
    manifest = json.loads((bundle / 'manifest.json').read_text())
    test, = request['tests']
    test_id = test['id']
    if not (bundle / 'DONE').is_file() or manifest.get('protocol') != 1 or manifest.get('mode') != 'dist':
        raise ValueError('incomplete bundle or incorrect protocol/mode')
    if (request['batch_id'] != BATCH_ID or manifest['batch_id'] != BATCH_ID
            or not request_commit or manifest['request_commit'] != request_commit
            or manifest['env_mismatch'] or manifest['limits_exceeded'] or manifest['tests'] != {test_id: 'ok'}):
        raise ValueError('wrong request, failed test, or incomplete GPU environment')
    if (test['frontend'] != 'triton-dist' or test['launcher'] != 'triton-dist'
            or test['ranks'] != 2 or test['repeats'] != 2
            or request['requires'] != {'sm': 90, 'gpus': 2, 'nodes': 1, 'env': 'triton-dist'}
            or env.mismatches(request['requires'], json.loads((bundle / 'env.json').read_text()))):
        raise ValueError('requires a pinned two-rank GPU launch')
    return check_outputs(test, bundle / test_id)


def check_outputs(test, root):
    from interp import gen_inputs, tensorfile
    meta = json.loads((root / 'meta.json').read_text())
    ranks, repeats = test['ranks'], test['repeats']
    if (ranks != 2 or meta['status'] != 'ok' or meta['launcher'] != test['launcher']
            or meta['ranks'] != ranks or meta['repeats'] != repeats or len(meta['runs']) != repeats):
        raise ValueError('unexpected launcher, ranks, repeats, or test status')
    refs = {}
    for spec in test['inputs']:
        value = gen_inputs.generate(spec['dtype'], spec['shape'], spec['gen'])
        digest = value.sha256()
        if spec['sha256'] != digest or meta['inputs'][spec['name']] != {
                'match': True, 'sha256': digest, 'expected_sha256': digest}:
            raise ValueError('input hash mismatch')
        refs[spec['name']] = value
    expected = {}
    for rank in range(ranks):
        key = f'rank{rank}/received'
        ref = refs[f'send{(rank - 1) % ranks}']
        digest = ref.sha256()
        expected[key] = digest
        path = root / 'out' / key
        if ({p.name for p in path.iterdir()} != {digest + '.tensor'}
                or tensorfile.read(path / (digest + '.tensor')) != ref):
            raise ValueError(f'{key}: stored tensor differs from the preceding rank input')
    for record in meta['runs']:
        if (record['status'] != 'ok' or record['exit_code'] != 0 or record['rank_status'] != ['ok'] * ranks
                or record['outputs'] != expected):
            raise ValueError('missing rank, wrong output, or failed repeat')
    if meta['distinct'] != {k: {digest: repeats} for k, digest in expected.items()}:
        raise ValueError('incorrect distinct output counts')
    return expected


if __name__ == '__main__':
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('bundle', type=Path)
    parser.add_argument('request_commit')
    args = parser.parse_args()
    for key, result in judge(BATCH, args.bundle, args.request_commit).items():
        print(f'{key}: exact {result}')
