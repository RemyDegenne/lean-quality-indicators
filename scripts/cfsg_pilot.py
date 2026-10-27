"""Pin AxiomMath/CFSG, select 2,000 files, and judge a 30-file Sonnet pilot.

The same repeated-proof-machinery protocol and source validator are used as in the
other libraries. No Lean code is executed. Certificates are excluded from sampling.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED
from collections import Counter
import fcntl
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time

import api_costs
import file_audits
import judge
import sample
import subscription_audits as runner

ROOT = Path(__file__).resolve().parent.parent
BASE = ROOT / 'runs/cfsg-pilot-2026-10-27'
SOURCE = ROOT / 'repos/axiom-cfsg'
COMMIT = '5f8042b343bddcb64d288f3e34a6831f12ca05b4'
AUDIT = 'repeated-proof-machinery'
LABEL = 'claude-sonnet-5-5-high'
LIBRARY = 'axiom-cfsg'
ORIGINAL_PROCESS = runner.process


def digest(data):
    return hashlib.sha256(data).hexdigest()


def dependencies():
    return json.loads((SOURCE / 'lake-manifest.json').read_text())['packages']


def source_dirs(row, mode='pinned'):
    if row['dir'] != 'axiom-cfsg':
        raise ValueError('Unexpected CFSG source root')
    dirs = {}
    for package in dependencies():
        name = package['name'].strip('«»')
        path = ROOT / 'repos/deps' / (name + '-' + package['rev'][:12])
        if subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=path, text=True).strip() != package['rev']:
            raise ValueError('Missing or changed pinned dependency: ' + str(path))
        dirs[f'{name} (pinned {package["rev"][:12]})'] = path
    toolchain = (SOURCE / 'lean-toolchain').read_text().strip()
    core = Path.home() / '.elan/toolchains' / toolchain.replace('/', '--').replace(':', '---') / 'src/lean'
    if not core.is_dir():
        raise ValueError('Missing Lean core source: ' + str(core))
    dirs['Lean core (' + toolchain + ')'] = core
    return SOURCE, dirs


def configure():
    # Reuse the existing subscription authentication, persistent attempts and
    # source/evidence verification, with an isolated corpus and result directory.
    runner.BASE = BASE
    runner.LIBRARIES = [LIBRARY]
    runner.AUDITS = [AUDIT]
    runner.sources = source_dirs
    runner.existing = lambda audit, sid: BASE / 'no-previous-pass' / (sid + '.json')
    judge.judge_dirs = source_dirs
    judge.build_message = file_audits.build_message
    judge.validate_verdict = file_audits.validate
    judge.codex_judge.run_process = process


def process(cmd, message, cwd, timeout):
    value = ORIGINAL_PROCESS(cmd, message, cwd, timeout)
    for line in value.stdout.splitlines():
        try:
            event = json.loads(line)
        except json.JSONDecodeError:
            continue
        if event.get('type') == 'rate_limit_event':
            info = event.get('rate_limit_info', {})
            if info.get('isUsingOverage') or info.get('status') == 'rejected':
                runner.STOP.set()
    return value


def prepare(selected=2000, limit=30):
    if subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=SOURCE, text=True).strip() != COMMIT:
        raise ValueError('CFSG source checkout moved')
    corpus = BASE / 'corpus'; corpus.mkdir(parents=True, exist_ok=True)
    config = '''[defaults]
exclude = ["*/Certificates/*"]
skip_deprecated = true
skip_private = true
[[library]]
id = "axiom-cfsg"
name = "CFSG (AxiomMath)"
[[library.source]]
dir = "axiom-cfsg"
url = "https://github.com/AxiomMath/CFSG"
include = ["CFSG/"]
exclude = []
'''
    (corpus / 'libraries.toml').write_text(config)
    runner.save(corpus / 'libraries.lock.json', {LIBRARY: {
        'library': LIBRARY, 'url': 'https://github.com/AxiomMath/CFSG', 'commit': COMMIT}})
    if not (corpus / 'repos').exists():
        (corpus / 'repos').symlink_to(ROOT / 'repos', target_is_directory=True)
    old = sample.ROOT, file_audits.ROOT, file_audits.RUBRICS
    try:
        sample.ROOT = file_audits.ROOT = corpus
        file_audits.RUBRICS = [AUDIT]
        rows, contract = file_audits.prepare(BASE, selected, 0, [LIBRARY])
    finally:
        sample.ROOT, file_audits.ROOT, file_audits.RUBRICS = old
    chosen = rows[:limit]
    directory = BASE / AUDIT / LABEL
    (directory / 'results').mkdir(parents=True, exist_ok=True)
    ind = BASE / 'protocols' / AUDIT
    protocol = {'backend': 'claude', 'model': 'claude-sonnet-5-5', 'effort': 'high',
        'audit': AUDIT, 'unit': 'file', 'account_label': 'lean-fro', 'billing': 'subscription_only',
        'commit': COMMIT, 'sample_ids': [r['id'] for r in chosen],
        'artifacts': {p.name: digest(p.read_bytes()) for p in ind.iterdir()},
        'code_hashes': {name: digest((ROOT / 'scripts' / name).read_bytes()) for name in
                        ['cfsg_pilot.py', 'judge.py', 'file_audits.py', 'source_tools.py', 'subscription_audits.py']}}
    manifest = directory / 'judge.json'
    if manifest.exists() and json.loads(manifest.read_text())['protocol'] != protocol:
        raise ValueError('Saved pilot selection or protocol changed')
    runner.save(manifest, {'protocol': protocol})
    runner.save(BASE / 'experiment.json', {'corpus': 'CFSG (AxiomMath)', 'commit': COMMIT,
        'selected_files': selected, 'pilot_files': limit, 'audit': AUDIT, 'model': 'claude-sonnet-5-5',
        'scope': 'CFSG/; certificate directories excluded by the common corpus rule',
        'candidate_files': contract['populations'][LIBRARY]['candidate_files'],
        'selection': 'Unchanged file-quality-v1 seed-zero SHA256 ordering and mathematical-declaration filter',
        'dependencies': dependencies(), 'tools': ['Read', 'Grep', 'Glob'], 'lean_execution': False})
    source_dirs(chosen[0])
    return rows, chosen


def report(rows):
    totals = runner.report(rows)
    experiment = json.loads((BASE / 'experiment.json').read_text())
    path = BASE / 'library-comparison.md'
    text = path.read_text().replace('# Library quality expansion', '# CFSG: repeated proof machinery pilot', 1)
    text = text.replace('Counts include the existing first pass, without rerunning or charging it again.',
        f"Pinned source: `{COMMIT}`. Selected {experiment['selected_files']:,} eligible files; "
        f"this pilot judges the first {experiment['pilot_files']} with the unchanged rubric. "
        'Sampling is restricted to CFSG/ and excludes certificate directories. Lean is not executed.')
    path.write_text(text)
    return totals


def verify(rows):
    return runner.verify_results(rows)


def run(chosen):
    usage = runner.quota(); runner.credentials()
    window = BASE / 'window.json'
    if not window.exists():
        runner.save(window, {'deadline': usage['week_all_models']['resets'], 'initial_usage': usage,
                            'account': 'lean-fro', 'jobs': 1, 'api_equivalent_ceiling_usd': 20})
    config = json.loads(window.read_text())
    attempts = Counter(); failures = []; todo = list(chosen); last_quota = time.time()
    directory = BASE / AUDIT / LABEL
    while todo and not runner.STOP.is_set():
        if time.time() - last_quota >= 60:
            usage = runner.quota(); last_quota = time.time()
        if not runner.admission_allowed(usage, config, time.time()):
            break
        row = todo.pop(0)
        if runner.result_for(row, AUDIT):
            continue
        api_costs.DIRECTORY_CACHE.pop(directory, None)
        spent = api_costs.directory_expenditure(directory)['api_usd']
        if spent + 5 > config['api_equivalent_ceiling_usd']:
            break
        attempts[row['id']] += 1
        with ThreadPoolExecutor(1) as pool:
            future = pool.submit(runner.review, row, AUDIT)
            while not future.done():
                totals = report(chosen)
                runner.save(BASE / 'status.json', {'stage': 'running', 'utc': file_audits.utc(),
                    'completed': totals[AUDIT + ':' + LIBRARY]['completed'], 'selected': len(chosen),
                    'active': 1, 'failures': failures, 'subscription_usage': usage})
                wait([future], timeout=30, return_when=FIRST_COMPLETED)
            try:
                value = future.result()
                print(json.dumps({'utc': file_audits.utc(), 'id': row['id'], 'verdict': value['verdict']}), flush=True)
            except Exception as exc:
                failures.append({'id': row['id'], 'error': str(exc), 'utc': file_audits.utc()})
                print(json.dumps(failures[-1]), flush=True)
                if attempts[row['id']] < 3 and not runner.STOP.is_set():
                    todo.append(row)
                else:
                    runner.STOP.set()
        time.sleep(3)
    totals = report(chosen)
    completed = totals[AUDIT + ':' + LIBRARY]['completed']
    verify(chosen)
    runner.save(BASE / 'status.json', {'stage': 'complete' if completed == len(chosen) else 'paused',
        'utc': file_audits.utc(), 'completed': completed, 'selected': len(chosen), 'active': 0, 'failures': failures})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--prepare-only', action='store_true')
    parser.add_argument('--report-only', action='store_true')
    args = parser.parse_args()
    configure(); BASE.mkdir(parents=True, exist_ok=True)
    with (BASE / 'controller.lock.log').open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        if args.report_only:
            rows = [json.loads(s) for s in (BASE / 'samples.jsonl').read_text().splitlines()]
            selected = set(json.loads((BASE / AUDIT / LABEL / 'judge.json').read_text())['protocol']['sample_ids'])
            report([r for r in rows if r['id'] in selected]); return
        _, chosen = prepare()
        if args.prepare_only:
            report(chosen); print('Prepared 2,000 eligible files; 30 selected for the Sonnet pilot.'); return
        run(chosen)


if __name__ == '__main__':
    main()
