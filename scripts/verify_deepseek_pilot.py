"""Read-only verification of selected targets, accepted verdicts and billed costs.

python3 scripts/verify_deepseek_pilot.py [--require-complete]
"""
import argparse
from collections import Counter
from decimal import Decimal
import hashlib
import json
from pathlib import Path
import subprocess

import deepseek_pilot as pilot
import duplicates_judge
import file_audits
import openrouter_judge
from source_tools import Sources


def verify():
    tasks = json.loads((pilot.BASE / 'selection.json').read_text())
    if tasks != pilot.selection():
        raise ValueError('Saved targets differ from the fixed corpus selections')
    results = {}
    for task in tasks:
        path = pilot.ROOT / task['output'] / 'results' / f"{task['row']['id']}.json"
        if path.exists():
            results[task['audit'], task['row']['id']] = json.loads(path.read_text())
    budget = json.loads((pilot.BASE / 'budget.json').read_text())
    billed = sum((Decimal(r['billed_usd']) for r in budget['requests'] if r['billed_usd'] is not None), Decimal(0))
    held = sum((Decimal(r['reserved_usd']) for r in budget['requests'] if r['billed_usd'] is None), Decimal(0))
    if billed != Decimal(budget['billed_usd']):
        raise ValueError('Recorded bill differs from request ledger')
    if billed + held > Decimal(budget['limit_usd']):
        raise ValueError('Billed requests plus pending reservations exceed spending cap')
    generations = {}
    for request in budget['requests']:
        generation = request.get('generation_id')
        if generation:
            if generation in generations:
                raise ValueError('Generation ID occurs twice in ledger')
            generations[generation] = request
    accepted = Counter()
    missing = []
    accepted_cost = Decimal(0)
    accepted_generations = set()
    commits = {}
    manifests = {}
    selection_hash = hashlib.sha256((pilot.BASE / 'selection.json').read_bytes()).hexdigest()
    seen = set()
    for task in tasks:
        row = task['row']
        key = (task['audit'], row['id'])
        if key in seen:
            raise ValueError('Target selected twice in one audit')
        seen.add(key)
        directory = pilot.ROOT / task['output']
        if directory not in manifests:
            protocol = json.loads((directory / 'judge.json').read_text())['protocol']
            if protocol['selection_sha256'] != selection_hash:
                raise ValueError('Judge manifest refers to another selection')
            selected = {t['row']['id'] for t in tasks if t['output'] == task['output']}
            if set(protocol['sample_ids']) != selected:
                raise ValueError('Judge manifest target IDs differ')
            ind = pilot.ROOT / task['indicator']
            artifacts = {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in ind.iterdir() if p.is_file()}
            if artifacts != protocol['artifacts']:
                raise ValueError('Audit prompt or schema changed')
            actual = {p.stem for p in (directory / 'results').glob('*.json') if p.stem.rsplit('-', 1)[-1].isdigit()}
            if not actual <= selected:
                raise ValueError('Unselected accepted result in model directory')
            manifests[directory] = protocol
        path = directory / 'results' / f"{row['id']}.json"
        if key not in results:
            missing.append({'audit': task['audit'], 'id': row['id']})
            continue
        result = results[key]
        if (result.get('id'), result.get('lib'), result.get('model'), result.get('backend'), result.get('effort')) != (
            row['id'], row['lib'], manifests[directory]['model'], 'openrouter', 'high'):
            raise ValueError(f'Result identity or model mismatch: {path}')
        if row['dir'] not in commits:
            commits[row['dir']] = subprocess.check_output(['git', 'rev-parse', 'HEAD'],
                cwd=pilot.ROOT / 'repos' / row['dir'], text=True).strip()
        if commits[row['dir']] != row['commit']:
            raise ValueError('Source checkout differs from pinned target')
        ind = pilot.ROOT / task['indicator']
        if task['unit'] == 'file':
            text = (pilot.ROOT / task['run'] / row['file']).read_text()
            if hashlib.sha256(text.encode()).hexdigest() != row['source_sha256']:
                raise ValueError('Source snapshot changed')
            cwd, dirs = pilot.sources(row, 'pinned')
            if hashlib.sha256((cwd / row['path']).read_bytes()).hexdigest() != row['source_sha256']:
                raise ValueError('Target source changed')
            file_audits.context.text = text
            file_audits.context.sources = Sources([cwd, *dirs.values()])
            schema_keys = json.loads((ind / 'schema.json').read_text())['required']
            file_audits.validate({k: result[k] for k in schema_keys}, ind)
        else:
            duplicates_judge.context.sample = row
            schema_keys = json.loads((ind / 'schema.json').read_text())['required']
            verdict = {k: result[k] for k in schema_keys}
            validate = duplicates_judge.validate if task['audit'].startswith('duplicates') else duplicates_judge.original_validate
            validate(verdict, ind)
        transcript = directory / 'results' / f"{row['id']}.attempt-{result['attempts']}.transcript.jsonl"
        raw = [json.loads(line)['response'] for line in transcript.read_text().splitlines()
               if json.loads(line).get('type') == 'api_response']
        raw = [response for response in raw if response.get('choices') and not response.get('error')]
        if [response['id'] for response in raw] != result['generation_ids']:
            raise ValueError('Accepted generations differ from saved API responses')
        original = openrouter_judge.parse_verdict(raw[-1]['choices'][0]['message']['content'])
        if original != {k: result[k] for k in schema_keys}:
            raise ValueError('Accepted verdict differs from model response')
        cost = Decimal(0)
        for generation in result['generation_ids']:
            if generation in accepted_generations:
                raise ValueError('Paid generation reused across accepted judgments')
            accepted_generations.add(generation)
            request = generations[generation]
            if request['target'] != row['id'] or request['model'] != result['model']:
                raise ValueError('Accepted generation belongs to another target/model')
            cost += Decimal(request['billed_usd'])
        if abs(cost - Decimal(str(result['cost_usd']))) > Decimal('0.000000001'):
            raise ValueError('Result cost differs from its paid generations')
        accepted_cost += cost
        accepted[task['audit']] += 1
    return {'planned': len(tasks), 'accepted': sum(accepted.values()), 'missing': len(missing),
            'accepted_by_audit': dict(accepted), 'billed_usd': str(billed),
            'accepted_judgment_usd': str(accepted_cost), 'other_billed_usd': str(billed - accepted_cost),
            'unsettled_reservations_usd': str(held), 'limit_usd': budget['limit_usd'],
            'missing_targets': missing}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--require-complete', action='store_true')
    args = parser.parse_args()
    report = verify()
    print(json.dumps(report, indent=2))
    if args.require_complete and report['missing']:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
