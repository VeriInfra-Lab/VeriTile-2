"""Judge a dispatch-variant result against the original two-rank GPU run (#457)."""
import json
from pathlib import Path
import sys

from dispatch_variant import SOURCE_RECORD
import judge

NAME = 'deepep-v1-variant-intranode-001'
RECORDED = Path(__file__).with_name('recorded-002.json')


def source_error(folder, test, original, changed):
    """Check every rank in every gpurun repeat against the independently pinned sources."""
    path = folder / 'stdout.log'
    if not path.is_file():
        return 'missing stdout.log'
    expected = {**original, **changed}
    ranks = set(range(test['ranks']))
    seen = []
    for line in path.read_text().splitlines():
        if line.startswith('== repeat '):
            if line != f'== repeat {len(seen)} ==':
                return 'unexpected repeat header'
            seen.append(set())
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
    return None


def compare_recorded(bundle, batch_dir=judge.BATCHES / NAME):
    bundle = Path(bundle)
    batch = json.loads((batch_dir / 'batch.json').read_text())
    tests = batch['tests']
    sources = json.loads(Path(__file__).with_name('source-sha256.json').read_text())
    changed = sources[batch['batch_id']]
    recorded = json.loads(RECORDED.read_text())
    results = judge.judge(batch_dir, bundle)
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
    results = compare_recorded(Path(sys.argv[1]))
    print(judge.render(results))
    raise SystemExit(0 if all(r['verdict'] == 'equal' for r in results) else 1)
