"""Extend OpenAI Math's Sonnet theorem audits from 100 to 300 fixed targets."""
import argparse
import fcntl
import json
import os
from pathlib import Path
import subprocess
import sys

import cfsg_theorem_audits as engine
import corpus_pilot as corpus
import file_audits
import judge
import subscription_audits as runner

ROOT = corpus.ROOT
PARENT = corpus.BASE / 'theorems'
BASE = corpus.BASE / 'scale-300/theorems'
AUDITS = engine.AUDITS
LABEL = engine.LABEL
CORPUS_NAME = 'OpenAI Math'
ORIGINAL_REPORT = engine.report
CODE = ['openai_scale.py', 'cfsg_theorem_audits.py', 'cfsg_pilot.py', 'corpus_pilot.py',
        'judge.py', 'duplicates_judge.py', 'codex_judge.py', 'subscription_audits.py']


def read_rows(base):
    return [json.loads(s) for s in (base / 'samples.jsonl').read_text().splitlines()]


def continuation(records, previous):
    if len(previous) != 100 or previous != [r['id'] for r in records[:100]]:
        raise ValueError('Expected the completed first 100 targets of the fixed selection')
    if len(records) < 300:
        raise ValueError('Insufficient frozen targets')
    return records[100:300]


def source_dirs(row, mode='pinned'):
    if row['lib'] != 'openai-math' or row['dir'] != 'openai-math':
        raise ValueError('Unexpected OpenAI source root')
    actual = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=corpus.SOURCE, text=True).strip()
    if actual != corpus.COMMIT:
        raise ValueError('OpenAI source checkout moved')
    for package in corpus.dependency_records():
        path = corpus.dependency_dir(package)
        actual = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=path, text=True).strip()
        if actual != package['rev']:
            raise ValueError('Pinned OpenAI dependency moved: ' + str(path))
    if mode == 'master':
        actual = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT / 'repos/mathlib', text=True).strip()
        if actual != json.loads((BASE / 'run.json').read_text())['mathlib_master_commit']:
            raise ValueError('Current-master Mathlib checkout moved')
    elif mode != 'pinned':
        raise ValueError('Unknown Mathlib mode')
    return corpus.source_dirs(row, mode)


def immutable_json(path, value):
    if path.exists() and json.loads(path.read_text()) != value:
        raise ValueError('Frozen continuation changed: ' + str(path))
    runner.save(path, value)


def prepare():
    BASE.mkdir(parents=True, exist_ok=True)
    records = read_rows(PARENT)
    previous = None
    for audit in AUDITS:
        manifest = PARENT / audit / LABEL / 'judge.json'
        protocol = json.loads(manifest.read_text())['protocol']
        ids = protocol['sample_ids']
        continuation(records, ids)
        if previous is not None and previous != ids:
            raise ValueError('Both audits must use the same theorem targets')
        previous = ids
        if any(not (manifest.parent / 'results' / (sid + '.json')).exists() for sid in ids):
            raise ValueError('Original pilot is incomplete')
    chosen = []
    for row in continuation(records, previous):
        snapshot = PARENT / row['file']
        chosen.append({**row, 'file': os.path.relpath(snapshot, BASE),
            'snippet_sha256': corpus.digest(snapshot.read_bytes()),
            'source_sha256': corpus.digest((corpus.SOURCE / row['path']).read_bytes())})
    text = ''.join(json.dumps(r, ensure_ascii=False) + '\n' for r in chosen)
    samples = BASE / 'samples.jsonl'
    if samples.exists() and samples.read_text() != text:
        raise ValueError('Continuation targets changed')
    samples.write_text(text)
    run = json.loads((PARENT / 'run.json').read_text())
    run['mathlib_master_commit'] = subprocess.check_output(
        ['git', 'rev-parse', 'HEAD'], cwd=ROOT / 'repos/mathlib', text=True).strip()
    run['dependencies'] = corpus.dependency_records()
    immutable_json(BASE / 'run.json', run)
    for audit in AUDITS:
        prior = PARENT / audit / LABEL / 'judge.json'
        original = json.loads(prior.read_text())['protocol']
        ind = BASE / 'protocols' / audit
        ind.mkdir(parents=True, exist_ok=True)
        for name, sha in original['artifacts'].items():
            data = (ROOT / 'indicators' / audit / name).read_bytes()
            if corpus.digest(data) != sha:
                raise ValueError('Original theorem rubric changed: ' + name)
            target = ind / name
            if target.exists() and target.read_bytes() != data:
                raise ValueError('Continuation rubric changed')
            target.write_bytes(data)
        protocol = {'backend': 'claude', 'model': 'claude-sonnet-5-5', 'effort': 'high',
            'audit': audit, 'unit': 'theorem', 'account_label': 'lean-fro', 'billing': 'subscription_only',
            'sample_ids': [r['id'] for r in chosen], 'target_coverage': 300, 'baseline_targets': 100,
            'selected_population_targets': len(records), 'sample_sha256': corpus.digest(samples.read_bytes()),
            'corpus': run, 'artifacts': original['artifacts'],
            'continued_from': {'manifest': str(prior.relative_to(ROOT)), 'sha256': corpus.digest(prior.read_bytes())},
            'code_hashes': {name: corpus.digest((ROOT / 'scripts' / name).read_bytes()) for name in CODE}}
        directory = BASE / audit / LABEL
        (directory / 'results').mkdir(parents=True, exist_ok=True)
        immutable_json(directory / 'judge.json', {'protocol': protocol})
    source_dirs(chosen[0], 'master')
    if not (BASE / 'window.json').exists():
        usage = runner.quota()
        runner.save(BASE / 'window.json', {'deadline': usage['week_all_models']['resets'],
            'initial_usage': usage, 'account': 'lean-fro', 'jobs': 1, 'api_equivalent_ceiling_usd': 40})
    return chosen


def configure():
    engine.BASE = BASE
    engine.corpus.SOURCE = corpus.SOURCE
    engine.source_dirs = source_dirs
    engine.report = report
    engine.verify = verify
    engine.configure()
    judge.build_message = file_audits.original_build_message


def selected_rows():
    return engine.selected_rows()


def result_for(row, audit):
    return engine.result_for(row, audit)


def report(chosen):
    totals = ORIGINAL_REPORT(chosen)
    path = BASE / 'library-comparison.md'
    text = path.read_text().replace('# CFSG: theorem audits', '# OpenAI Math: expanded theorem audits', 1)
    text = text.replace('The same 30 theorems', 'The same 200 additional theorems')
    text = text.replace('Scope: CFSG/ excluding certificate directories.', 'Scope: lean/OAI/; the original corpus selection is unchanged.')
    text = text.replace('CFSG’s pinned Mathlib', 'OpenAI Math’s pinned Mathlib')
    text += '\nThese counts cover targets 101–300. Main library comparisons include the original 100 judgments per audit.\n'
    path.write_text(text)
    return totals


ORIGINAL_VERIFY = engine.verify


def verify(chosen):
    for audit in AUDITS:
        protocol = json.loads((BASE / audit / LABEL / 'judge.json').read_text())['protocol']
        prior = ROOT / protocol['continued_from']['manifest']
        assert corpus.digest(prior.read_bytes()) == protocol['continued_from']['sha256']
    return ORIGINAL_VERIFY(chosen)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--prepare-only', action='store_true')
    parser.add_argument('--report-only', action='store_true')
    parser.add_argument('--watch', action='store_true')
    args = parser.parse_args()
    if args.watch:
        import watch_cfsg_theorems as watcher
        watcher.pilot = sys.modules[__name__]
        watcher.main()
        return
    BASE.mkdir(parents=True, exist_ok=True)
    if args.report_only:
        configure()
        chosen = selected_rows()
        verify(chosen)
        report(chosen)
        return
    with (BASE / 'controller.lock.log').open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        chosen = prepare()
        configure()
        if args.prepare_only:
            verify(chosen)
            report(chosen)
        else:
            engine.run(chosen)


if __name__ == '__main__':
    main()
