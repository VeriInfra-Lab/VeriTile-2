"""Judge a dispatch-variant result against the original two-rank GPU run (#457)."""
import argparse
import json
from pathlib import Path

from dispatch_variant import SOURCE_RECORD
import judge

NAME = 'deepep-v1-variant-intranode-001'
SMALL_RING = 'deepep-v1-variant-intranode-003'
RECORDED = Path(__file__).with_name('recorded-002.json')
RECORDED_LIMIT = (
    'With these inputs the head stores at DD 511 and DC 265 are never waited on (thresholds are negative). '
    '`equal` shows that the patched source compiles and completes; the memory-order change cannot be confirmed by comparing outputs.'
)


def source_error(folder, test, original, changed):
    """Check every rank in every gpurun repeat against the independently pinned sources."""
    path = folder / 'stdout.log'
    if not path.is_file():
        return 'missing stdout.log'
    expected = {**original, **changed}
    ranks = set(range(test['ranks']))
    seen = []
    rings = []
    for line in path.read_text().splitlines():
        if line.startswith('== repeat '):
            if line != f'== repeat {len(seen)} ==':
                return 'unexpected repeat header'
            seen.append(set())
            rings.append([])
        elif line.startswith('deepep-ring '):
            if not rings:
                return 'ring configuration outside a repeat'
            rings[-1].append(line)
        elif line.startswith(SOURCE_RECORD):
            try:
                record = json.loads(line[len(SOURCE_RECORD):])
                rank, files = record['rank'], record['files']
            except (ValueError, KeyError, TypeError):
                return 'invalid source hash record'
            if not seen or type(rank) is not int or rank not in ranks or rank in seen[-1]:
                return 'unexpected or duplicate rank in source hash records'
            if not isinstance(files, dict):
                return f'rank {rank} has no source hash map'
            for name in changed:
                if files.get(name) == original[name]:
                    return f'repeat {len(seen) - 1}, rank {rank}: {name} has the original hash'
            if files != expected:
                return f'repeat {len(seen) - 1}, rank {rank}: materialized files or hashes differ from the pin'
            seen[-1].add(rank)
    if len(seen) != test['repeats'] or any(group != ranks for group in seen):
        return 'missing rank or repeat source hash records'
    if 'ring' in test.get('launch', {}):
        ring = test['launch']['ring']
        expected_lines = sorted(f'deepep-ring rank={r} channels={ring["num_sms"] // 2} '
                                f'dispatch=24/{ring["recv_tokens"]} combine={ring["combine_send_tokens"]}/{ring["recv_tokens"]}' for r in ranks)
        if any(sorted(group) != expected_lines for group in rings):
            return 'missing or incorrect executed ring configuration'
    return None


def compare_recorded(bundle, batch_dir=judge.BATCHES / NAME):
    bundle = Path(bundle)
    batch = json.loads((batch_dir / 'batch.json').read_text())
    tests = batch.get('tests')
    if not isinstance(tests, list) or not tests:
        raise ValueError('no test results to judge: the batch has no tests')
    sources = json.loads(Path(__file__).with_name('source-sha256.json').read_text())
    changed = sources[NAME if batch['batch_id'] == SMALL_RING else batch['batch_id']]
    recorded = json.loads(RECORDED.read_text())
    results = judge.judge(batch_dir, bundle)
    if not results or len(results) != len(tests) or all(r['status'] == 'not_run' for r in results):
        raise ValueError('missing test results: one judgment per batch test is required')
    for test, result in zip(tests, results):
        if result['status'] != 'ok':
            continue
        folder = bundle / test['id']
        meta = json.loads((folder / 'meta.json').read_text())
        error = source_error(folder, test, sources['original'], changed)
        if error is not None:
            result['differences'].append({'output': 'source hashes', 'error': error})
        hashes = recorded[test['id']]
        inputs = {i['name']: i['sha256'] for i in test['inputs']}
        if (meta['status'] != 'ok' or meta['ranks'] != test['ranks'] or meta['repeats'] != test['repeats'] or
                {k: v['sha256'] for k, v in meta['inputs'].items()} != inputs or
                set(meta['distinct']) != set(hashes)):
            result['differences'].append({'output': 'metadata', 'error': 'ranks, repeats, inputs or output keys differ'})
        for key, original in hashes.items():
            # judge.judge also reads the complete .tensor file and validates its SHA-256.
            seen = meta['distinct'].get(key)
            if seen != {original: test['repeats']}:
                result['differences'].append({'output': key, 'recorded_sha256': original, 'found': seen})
        result['verdict'] = 'different' if result['differences'] else 'equal'
    return results


if __name__ == '__main__':
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument('bundle', type=Path)
    cli.add_argument('--batch', choices=[NAME, 'deepep-v1-variant-intranode-002', SMALL_RING], default=NAME)
    args = cli.parse_args()
    try:
        results = compare_recorded(args.bundle, judge.BATCHES / args.batch)
    except KeyError as exc:
        cli.exit(1, f'Missing result data: {exc}\n')
    except (OSError, ValueError) as exc:
        cli.exit(1, f'Cannot judge result bundle: {exc}\n')
    if args.batch == NAME:
        print(RECORDED_LIMIT)
    print(judge.render(results))
    raise SystemExit(0 if all(r['verdict'] == 'equal' for r in results) else 1)
