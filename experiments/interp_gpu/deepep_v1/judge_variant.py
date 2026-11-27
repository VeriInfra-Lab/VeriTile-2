"""Judge a dispatch-variant result against the original two-rank GPU run (#457)."""
import json
from pathlib import Path
import sys

import judge

NAME = 'deepep-v1-variant-intranode-001'
RECORDED = Path(__file__).with_name('recorded-002.json')


def compare_recorded(bundle, batch_dir=judge.BATCHES / NAME):
    bundle = Path(bundle)
    tests = json.loads((batch_dir / 'batch.json').read_text())['tests']
    recorded = json.loads(RECORDED.read_text())
    results = judge.judge(batch_dir, bundle)
    for test, result in zip(tests, results):
        if result['status'] != 'ok':
            continue
        folder = bundle / test['id']
        meta = json.loads((folder / 'meta.json').read_text())
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
