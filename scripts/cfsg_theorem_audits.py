"""Run Remy's two theorem audits on a fixed CFSG sample, using the lean-fro subscription."""
import argparse
from collections import Counter
from concurrent.futures import ThreadPoolExecutor, wait
import fcntl
import json
import random
import re
import subprocess
import time

import api_costs
import cfsg_pilot as corpus
import duplicates_judge
import indicator
import judge
import sample
import subscription_audits as runner
from report import wilson

ROOT = corpus.ROOT
BASE = corpus.BASE / 'theorems'
AUDITS = ['unnecessary-hypotheses', 'duplicates-mathlib-inclusive']
LABEL = corpus.LABEL
LIBRARY = corpus.LIBRARY
CODE = ['cfsg_theorem_audits.py', 'cfsg_pilot.py', 'judge.py', 'duplicates_judge.py',
        'codex_judge.py', 'subscription_audits.py', 'sample.py', 'leanscan.py']


def rows():
    return [json.loads(s) for s in (BASE / 'samples.jsonl').read_text().splitlines()]


def source_dirs(row, mode='pinned'):
    cwd, dirs = corpus.source_dirs(row, 'pinned')
    if mode == 'master':
        dirs = {k: v for k, v in dirs.items() if not k.startswith('mathlib (')}
        path = ROOT / 'repos/mathlib'
        actual = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=path, text=True).strip()
        expected = json.loads((BASE / 'run.json').read_text())['mathlib_master_commit']
        if actual != expected:
            raise ValueError('Current-master Mathlib checkout moved since preparation')
        dirs['Mathlib (current master, commit ' + actual[:12] + ')'] = path
    elif mode != 'pinned':
        raise ValueError('Unknown Mathlib mode: ' + mode)
    return cwd, dirs


def configure():
    runner.BASE = BASE
    judge.judge_dirs = source_dirs
    judge.codex_judge.run_process = process


def process(cmd, message, cwd, timeout):
    value = corpus.process(cmd, message, cwd, timeout)
    # Stop admission even if a rejected request also produced a result event.
    if runner.STOP.is_set() or re.search(r'rate_limit_error|too many requests|(?:HTTP\S*\s+|status(?:_code)?[=: ]+)429\b',
                                       value.stdout + value.stderr, re.I):
        runner.STOP.set()
        raise RuntimeError('Rate limit or overage rejection; pilot paused')
    return value


def prepare(selected=2000, limit=30):
    BASE.mkdir(parents=True, exist_ok=True)
    actual = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=corpus.SOURCE, text=True).strip()
    if actual != corpus.COMMIT:
        raise ValueError('CFSG checkout moved')
    destination = BASE / 'samples.jsonl'
    if not destination.exists():
        old = sample.ROOT
        try:
            sample.ROOT = corpus.BASE / 'corpus'
            cfg, lock = sample.load_config()
            population, info = sample.population(cfg, lock, cfg['library'][0], 8)
            picked = sample.draw(random.Random('0:' + LIBRARY), len(population), selected)
            if len(picked) != selected:
                raise ValueError('Insufficient theorem population')
            records = []
            for index, number in enumerate(picked):
                row = population[number]
                sid = f'{LIBRARY}-{index:04d}'
                snippet, _ = sample.extract(lock, cfg['library'][0]['source'][0], row)
                target = f'samples/{LIBRARY}/{sid}.lean'
                path = BASE / target
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(snippet)
                records.append({'id': sid, **row, 'commit': corpus.COMMIT, 'file': target,
                    'source_sha256': corpus.digest((corpus.SOURCE / row['path']).read_bytes()),
                    'snippet_sha256': corpus.digest(snippet.encode()),
                    'url': f'https://github.com/AxiomMath/CFSG/blob/{corpus.COMMIT}/{row["path"]}#L{row["line"]}'})
        finally:
            sample.ROOT = old
        master = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT / 'repos/mathlib', text=True).strip()
        runner.save(BASE / 'run.json', {'seed': 0, 'n': selected, 'population': {LIBRARY: info},
            'commit': corpus.COMMIT, 'mathlib_master_commit': master,
            'selection': 'Original prefix-stable theorem sampler, seed 0:axiom-cfsg; CFSG/ excluding certificate directories',
            'dependencies': corpus.dependencies()})
        temporary = destination.with_suffix('.tmp')
        temporary.write_text(''.join(json.dumps(r, ensure_ascii=False) + '\n' for r in records))
        temporary.replace(destination)
    records = rows()
    if len(records) != selected or not 1 <= limit <= selected:
        raise ValueError('Saved selection size differs')
    chosen = records[:limit]
    for audit in AUDITS:
        ind = BASE / 'protocols' / audit
        ind.mkdir(parents=True, exist_ok=True)
        for name in ['prompt.md', 'message.md', 'schema.json', 'config.toml']:
            data = (ROOT / 'indicators' / audit / name).read_bytes()
            target = ind / name
            if target.exists() and target.read_bytes() != data:
                raise ValueError('Frozen theorem protocol changed')
            target.write_bytes(data)
        directory = BASE / audit / LABEL
        (directory / 'results').mkdir(parents=True, exist_ok=True)
        protocol = {'backend': 'claude', 'model': 'claude-sonnet-5-5', 'effort': 'high',
            'audit': audit, 'unit': 'theorem', 'account_label': 'lean-fro', 'billing': 'subscription_only',
            'sample_ids': [r['id'] for r in chosen], 'selected_population_targets': selected,
            'sample_sha256': corpus.digest(destination.read_bytes()),
            'corpus': json.loads((BASE / 'run.json').read_text()),
            'artifacts': {p.name: corpus.digest(p.read_bytes()) for p in ind.iterdir() if p.is_file()},
            'code_hashes': {name: corpus.digest((ROOT / 'scripts' / name).read_bytes()) for name in CODE}}
        manifest = directory / 'judge.json'
        if manifest.exists() and json.loads(manifest.read_text())['protocol'] != protocol:
            raise ValueError('Saved judge selection or protocol changed')
        runner.save(manifest, {'protocol': protocol})
    source_dirs(chosen[0], 'master')
    return chosen


def selected_rows():
    selected = set(json.loads((BASE / AUDITS[0] / LABEL / 'judge.json').read_text())['protocol']['sample_ids'])
    for audit in AUDITS[1:]:
        if selected != set(json.loads((BASE / audit / LABEL / 'judge.json').read_text())['protocol']['sample_ids']):
            raise ValueError('The two audits must use the same targets')
    return [r for r in rows() if r['id'] in selected]


def result_for(row, audit):
    path = BASE / audit / LABEL / 'results' / (row['id'] + '.json')
    return json.loads(path.read_text()) if path.exists() else None


def validate(verdict, ind, row):
    duplicates_judge.context.sample = row
    try:
        if ind.name.startswith('duplicates'):
            duplicates_judge.validate(verdict, ind)
        else:
            duplicates_judge.original_validate(verdict, ind)
    finally:
        del duplicates_judge.context.sample


def review(row, audit):
    directory = BASE / audit / LABEL / 'results'
    ind = BASE / 'protocols' / audit
    if corpus.digest((BASE / row['file']).read_bytes()) != row['snippet_sha256']:
        raise ValueError('Theorem snapshot changed')
    if corpus.digest((corpus.SOURCE / row['path']).read_bytes()) != row['source_sha256']:
        raise ValueError('Theorem source changed')
    attempt = judge.codex_judge.next_attempt(directory, row['id'])
    runner.LOCAL.output = directory / (row['id'] + '.live.jsonl')
    runner.LOCAL.errors = directory / (row['id'] + '.live.stderr.log')
    runner.LOCAL.attempt_output = directory / f'{row["id"]}.attempt-{attempt}.transcript.jsonl'
    runner.LOCAL.attempt_errors = directory / f'{row["id"]}.attempt-{attempt}.stderr.log'
    judge.validate_verdict = lambda verdict, protocol: validate(verdict, protocol, row)
    args = argparse.Namespace(backend='claude', model='claude-sonnet-5-5', effort='high',
                              claude='claude', timeout=1200, retries=0, max_budget=5)
    value = judge.judge_one(row, BASE, ind, directory, args)
    value.update(subscription_account='lean-fro', billing='subscription', actual_api_charge_usd=0)
    runner.save(directory / (row['id'] + '.json'), value)
    (directory / (row['id'] + '.failure.json')).unlink(missing_ok=True)
    return value


def report(chosen):
    totals = {}
    lines = ['# CFSG: theorem audits', '',
        'Sonnet 5.5, high effort. The same 30 theorems from a fixed 2,000-target selection are used for both audits. '
        'Scope: CFSG/ excluding certificate directories. Flags are judge claims; Lean is not executed.', '',
        '| Audit | Reviewed | Flagged | Rate (95% CI) | API equivalent spent |', '|---|---:|---:|---:|---:|']
    for audit in AUDITS:
        values = [result_for(r, audit) for r in chosen]
        values = [v for v in values if v]
        positive = indicator.config(BASE / 'protocols' / audit)['positive']
        flagged = sum(v['verdict'] in positive for v in values)
        n = len(values)
        ci = wilson(flagged, n) if n else None
        directory = BASE / audit / LABEL
        api_costs.DIRECTORY_CACHE.pop(directory, None)
        cost = api_costs.directory_expenditure(directory)
        totals[audit] = {'selected': len(chosen), 'completed': n, 'flagged': flagged,
                        'ci95': ci, 'expenditure': cost}
        rate = f'{flagged/n:.1%} [{ci[0]:.1%}, {ci[1]:.1%}]' if n else '—'
        lines.append(f'| {audit} | {n}/{len(chosen)} | {flagged} | {rate} | ${cost["api_usd"]:.2f} |')
    lines += ['', 'Subscription account lean-fro; actual API charges $0. '
              'Hypotheses checks use current-master Mathlib, frozen at preparation; duplication uses CFSG’s pinned Mathlib. '
              'The original prompts, schemas and validators are unchanged.']
    (BASE / 'library-comparison.md').write_text('\n'.join(lines) + '\n')
    runner.save(BASE / 'library-comparison.json', totals)
    return totals


def verify(chosen):
    counts = Counter()
    for audit in AUDITS:
        ind = BASE / 'protocols' / audit
        manifest = json.loads((BASE / audit / LABEL / 'judge.json').read_text())['protocol']
        assert manifest['sample_ids'] == [r['id'] for r in chosen]
        assert manifest['sample_sha256'] == corpus.digest((BASE / 'samples.jsonl').read_bytes())
        for name, sha in manifest['artifacts'].items():
            assert corpus.digest((ind / name).read_bytes()) == sha
        for name, sha in manifest['code_hashes'].items():
            assert corpus.digest((ROOT / 'scripts' / name).read_bytes()) == sha
        source_dirs(chosen[0], indicator.config(ind)['mathlib'])
        for row in chosen:
            value = result_for(row, audit)
            if not value:
                continue
            assert corpus.digest((BASE / row['file']).read_bytes()) == row['snippet_sha256']
            assert corpus.digest((corpus.SOURCE / row['path']).read_bytes()) == row['source_sha256']
            assert value['model'] == 'claude-sonnet-5-5' and value['effort'] == 'high'
            assert value['subscription_account'] == 'lean-fro' and value['actual_api_charge_usd'] == 0
            directory = BASE / audit / LABEL / 'results'
            raw = json.loads((directory / (row['id'] + '.raw.json')).read_text())
            verdict = raw['structured_output']
            validate(verdict, ind, row)
            assert all(value[k] == v for k, v in verdict.items())
            events = [json.loads(s) for s in (directory / (row['id'] + '.transcript.jsonl')).read_text().splitlines()]
            initial = next(e for e in events if e.get('type') == 'system' and e.get('subtype') == 'init')
            assert set(initial['tools']) <= {'Read', 'Grep', 'Glob', 'StructuredOutput'}
            assert initial['model'] == 'claude-sonnet-5-5' and initial['apiKeySource'] == 'none'
            for event in events:
                if event.get('type') == 'rate_limit_event':
                    assert not event['rate_limit_info'].get('isUsingOverage', False)
            counts[audit] += 1
    result = {'checked_utc': corpus.file_audits.utc(), 'accepted': sum(counts.values()),
              'by_audit': dict(counts), 'checks': ['source and snippet hashes', 'frozen protocols and code',
                  'schema and duplicate invariants', 'raw structured output', 'read-only tools', 'subscription billing']}
    runner.save(BASE / 'verification.json', result)
    return result


def run(chosen):
    usage = runner.quota()
    runner.credentials()
    window = BASE / 'window.json'
    if not window.exists():
        runner.save(window, {'deadline': usage['week_all_models']['resets'], 'initial_usage': usage,
            'account': 'lean-fro', 'jobs': 1, 'api_equivalent_ceiling_usd': 20})
    config = json.loads(window.read_text())
    todo = [(row, audit) for row in chosen for audit in AUDITS if not result_for(row, audit)]
    failures = []
    attempts = Counter()
    last_quota = time.time()

    def status(stage, active):
        totals = report(chosen)
        runner.save(BASE / 'status.json', {'stage': stage, 'utc': corpus.file_audits.utc(),
            'completed': sum(v['completed'] for v in totals.values()), 'selected': len(chosen) * len(AUDITS),
            'by_audit': totals, 'active': active, 'failures': failures, 'subscription_usage': usage})

    status('running', 0)
    while todo and not runner.STOP.is_set():
        if time.time() - last_quota >= 60:
            usage = runner.quota()
            last_quota = time.time()
        if not runner.admission_allowed(usage, config, time.time()):
            break
        totals = report(chosen)
        if sum(v['expenditure']['api_usd'] for v in totals.values()) + 5 > config['api_equivalent_ceiling_usd']:
            break
        row, audit = todo.pop(0)
        directory = BASE / audit / LABEL / 'results'
        key = (row['id'], audit)
        attempts[key] = max(attempts[key], judge.codex_judge.next_attempt(directory, row['id']) - 1) + 1
        if attempts[key] > 3:
            runner.STOP.set()
            break
        with ThreadPoolExecutor(1) as pool:
            future = pool.submit(review, row, audit)
            while not future.done():
                status('running', 1)
                wait([future], timeout=30)
            try:
                value = future.result()
                print(json.dumps({'audit': audit, 'id': row['id'], 'verdict': value['verdict']}), flush=True)
            except Exception as exc:
                failure = {'audit': audit, 'id': row['id'], 'error': str(exc), 'utc': corpus.file_audits.utc()}
                failures.append(failure)
                runner.save(directory / (row['id'] + '.failure.json'), failure)
                print(json.dumps(failure), flush=True)
                if isinstance(exc, RuntimeError) and attempts[key] < 3 and not runner.STOP.is_set():
                    todo.append((row, audit))
                else:
                    runner.STOP.set()
        time.sleep(3)
    verify(chosen)
    complete = all(result_for(r, a) for r in chosen for a in AUDITS)
    status('complete' if complete else 'paused', 0)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--prepare-only', action='store_true')
    parser.add_argument('--report-only', action='store_true')
    args = parser.parse_args()
    configure()
    BASE.mkdir(parents=True, exist_ok=True)
    with (BASE / 'controller.lock.log').open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        chosen = selected_rows() if args.report_only else prepare()
        if args.prepare_only or args.report_only:
            report(chosen)
            verify(chosen)
        else:
            run(chosen)


if __name__ == '__main__':
    main()
