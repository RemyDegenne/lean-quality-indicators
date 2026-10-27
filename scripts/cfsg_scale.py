"""Continue each CFSG audit to 300 targets without changing or rerunning its first 30."""
import argparse
import fcntl
import json
import os
from pathlib import Path

import api_costs
import cfsg_pilot as files
import cfsg_theorem_audits as theorems
import file_audits
import indicator
import judge
import subscription_audits as runner
from report import wilson

ROOT = files.ROOT
PARENT = files.BASE
BASE = PARENT / 'scale-300'
LABEL = files.LABEL
ORIGINAL_REPORT = {'file': files.report, 'theorem': theorems.report}
ORIGINAL_VERIFY = {'file': files.verify, 'theorem': theorems.verify}
LIMIT = 300
CEILINGS = {'file': 60, 'theorem': 50}


def origin(unit):
    return PARENT if unit == 'file' else PARENT / 'theorems'


def destination(unit):
    return BASE / ('files' if unit == 'file' else 'theorems')


def audits(unit):
    return [files.AUDIT] if unit == 'file' else theorems.AUDITS


def read_rows(base):
    return [json.loads(s) for s in (base / 'samples.jsonl').read_text().splitlines()]


def continuation(records, previous, total=LIMIT):
    if previous != [r['id'] for r in records[:len(previous)]]:
        raise ValueError('Existing audit is not the prefix of the frozen selection')
    if not len(previous) < total <= len(records):
        raise ValueError('Invalid expanded coverage')
    return records[len(previous):total]


def immutable_json(path, value):
    if path.exists() and json.loads(path.read_text()) != value:
        raise ValueError('Frozen continuation changed: ' + str(path))
    runner.save(path, value)


def prepare(unit):
    parent = origin(unit)
    base = destination(unit)
    base.mkdir(parents=True, exist_ok=True)
    records = read_rows(parent)
    prior_ids = None
    for audit in audits(unit):
        prior = parent / audit / LABEL / 'judge.json'
        protocol = json.loads(prior.read_text())['protocol']
        ids = protocol['sample_ids']
        if len(ids) != 30 or (prior_ids is not None and ids != prior_ids):
            raise ValueError('Expected the same completed 30-target baseline')
        prior_ids = ids
        if any(not (prior.parent / 'results' / (sid + '.json')).exists() for sid in ids):
            raise ValueError('Initial pilot must be complete before continuation')
        for name, sha in protocol['code_hashes'].items():
            if files.digest((ROOT / 'scripts' / name).read_bytes()) != sha:
                raise ValueError('Baseline runner changed: ' + name)
    chosen = continuation(records, prior_ids)
    chosen = [{**r, 'file': os.path.relpath(parent / r['file'], base)} for r in chosen]
    samples = ''.join(json.dumps(r, ensure_ascii=False) + '\n' for r in chosen)
    path = base / 'samples.jsonl'
    if path.exists() and path.read_text() != samples:
        raise ValueError('Continuation sample changed')
    path.write_text(samples)
    immutable_json(base / 'run.json', json.loads((parent / 'run.json').read_text()))
    for audit in audits(unit):
        prior = parent / audit / LABEL / 'judge.json'
        original = json.loads(prior.read_text())['protocol']
        ind = base / 'protocols' / audit
        ind.mkdir(parents=True, exist_ok=True)
        for name, sha in original['artifacts'].items():
            data = (parent / 'protocols' / audit / name).read_bytes()
            if files.digest(data) != sha:
                raise ValueError('Original rubric changed')
            target = ind / name
            if target.exists() and target.read_bytes() != data:
                raise ValueError('Continuation rubric changed')
            target.write_bytes(data)
        protocol = {**original, 'sample_ids': [r['id'] for r in chosen],
            'sample_sha256': files.digest(path.read_bytes()), 'selected_population_targets': len(records),
            'target_coverage': LIMIT, 'baseline_targets': len(prior_ids),
            'continued_from': {'manifest': str(prior.relative_to(ROOT)), 'sha256': files.digest(prior.read_bytes())},
            'code_hashes': {**original['code_hashes'], 'cfsg_scale.py': files.digest(Path(__file__).read_bytes())}}
        directory = base / audit / LABEL
        (directory / 'results').mkdir(parents=True, exist_ok=True)
        immutable_json(directory / 'judge.json', {'protocol': protocol})
    if unit == 'file':
        experiment = json.loads((parent / 'experiment.json').read_text())
        immutable_json(base / 'experiment.json', {**experiment, 'pilot_files': len(chosen),
            'target_coverage': LIMIT, 'baseline_files': len(prior_ids)})
    if not (base / 'window.json').exists():
        usage = runner.quota()
        runner.save(base / 'window.json', {'deadline': usage['week_all_models']['resets'],
            'initial_usage': usage, 'account': 'lean-fro', 'jobs': 1,
            'api_equivalent_ceiling_usd': CEILINGS[unit]})
    return chosen


def report(unit, chosen):
    totals = ORIGINAL_REPORT[unit](chosen)
    path = destination(unit) / 'library-comparison.md'
    text = path.read_text()
    if unit == 'file':
        text = text.replace('this pilot judges the first 270', 'this continuation judges targets 31–300')
    else:
        text = text.replace('The same 30 theorems', 'The same 270 additional theorems')
    text += '\nThese counts cover the 270 additional targets. The main library comparisons combine them with the original 30.\n'
    path.write_text(text)
    return totals


def verify(unit, chosen):
    base = destination(unit)
    for audit in audits(unit):
        protocol = json.loads((base / audit / LABEL / 'judge.json').read_text())['protocol']
        assert protocol['sample_ids'] == [r['id'] for r in chosen]
        assert protocol['sample_sha256'] == files.digest((base / 'samples.jsonl').read_bytes())
        prior = ROOT / protocol['continued_from']['manifest']
        assert files.digest(prior.read_bytes()) == protocol['continued_from']['sha256']
        for name, sha in protocol['code_hashes'].items():
            assert files.digest((ROOT / 'scripts' / name).read_bytes()) == sha
        for name, sha in protocol['artifacts'].items():
            assert files.digest((base / 'protocols' / audit / name).read_bytes()) == sha
    return ORIGINAL_VERIFY[unit](chosen)


def configure(unit):
    files.BASE = destination('file')
    theorems.BASE = destination('theorem')
    module = files if unit == 'file' else theorems
    module.configure()
    if unit == 'theorem':
        judge.build_message = file_audits.original_build_message
    # Apply the same explicit 429/overage stop to both workers.
    judge.codex_judge.run_process = theorems.process
    module.report = lambda chosen: report(unit, chosen)
    module.verify = lambda chosen: verify(unit, chosen)
    return module


def summary():
    lines = ['# CFSG expanded coverage', '',
        'Sonnet 5.5 high; first-pass totals include the original 30 targets and the next 270 from each fixed selection.', '',
        '| Audit | Reviewed / planned | Flagged | Rate (95% CI) | API equivalent spent |',
        '|---|---:|---:|---:|---:|']
    totals = {}
    for unit in ('file', 'theorem'):
        records = read_rows(origin(unit))[:LIMIT]
        for audit in audits(unit):
            values = []
            spent = 0
            for base in (origin(unit), destination(unit)):
                directory = base / audit / LABEL
                api_costs.DIRECTORY_CACHE.pop(directory, None)
                spent += api_costs.directory_expenditure(directory)['api_usd']
                values += [json.loads(p.read_text()) for r in records
                           if (p := directory / 'results' / (r['id'] + '.json')).exists()]
            if len({v['id'] for v in values}) != len(values):
                raise ValueError('Continuation reran a baseline target')
            positive = indicator.config(origin(unit) / 'protocols' / audit)['positive']
            flagged = sum(bool(v['findings']) if unit == 'file' else v['verdict'] in positive for v in values)
            n = len(values)
            lo, hi = wilson(flagged, n)
            totals[audit] = {'completed': n, 'selected': LIMIT, 'flagged': flagged, 'ci95': [lo, hi], 'api_equivalent_usd': spent}
            lines.append(f'| {audit} | {n}/{LIMIT} | {flagged} | {flagged/n:.1%} [{lo:.1%}, {hi:.1%}] | ${spent:.2f} |')
    lines += ['', 'Subscription account lean-fro; actual API charges $0.']
    (BASE / 'progress.md').write_text('\n'.join(lines) + '\n')
    runner.save(BASE / 'progress.json', totals)
    return totals


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('unit', choices=['file', 'theorem'])
    parser.add_argument('--prepare-only', action='store_true')
    parser.add_argument('--report-only', action='store_true')
    args = parser.parse_args()
    base = destination(args.unit)
    base.mkdir(parents=True, exist_ok=True)
    if args.report_only:
        chosen = read_rows(base)
        configure(args.unit)
        verify(args.unit, chosen)
        return
    with (base / 'controller.lock.log').open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        chosen = prepare(args.unit)
        module = configure(args.unit)
        if args.prepare_only:
            verify(args.unit, chosen)
            report(args.unit, chosen)
        else:
            module.run(chosen)


if __name__ == '__main__':
    main()
