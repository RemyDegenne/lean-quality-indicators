"""Spend only the pinned lean-fro subscription window on balanced library audits."""
import argparse
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED
from collections import Counter
import datetime as dt
import fcntl
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import threading
import time

import corpus_pilot
import file_audits
import judge
import sample
from report import wilson

ROOT = Path(__file__).resolve().parent.parent
BASE = ROOT / 'runs/library-quality-scale-2026-10-26'
LIBRARIES = ['mathlib', 'tauceti', 'formal-frontier', 'lean-pool', 'flt-anthropic', 'openai-math']
AUDITS = ['concept-reinvention', 'repeated-proof-machinery', 'simp-interface']
LABEL = 'claude-sonnet-5-5-high'
USAGE = Path.home() / '.claude/skills/claude-usage/claude-usage'
LOCAL = threading.local()
STOP = threading.Event()
ORIGINAL_DIRS = judge.judge_dirs


def save(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + f'.{os.getpid()}.tmp')
    temporary.write_text(json.dumps(value, indent=2) + '\n')
    temporary.replace(path)


def quota():
    result = subprocess.run([str(USAGE), '--account', 'lean-fro', '--ttl', '60', '--no-stale'],
                            capture_output=True, text=True, timeout=25, check=True)
    value = json.loads(result.stdout)
    if value.get('extra_usage', {}).get('is_enabled'):
        raise RuntimeError('Extra usage is enabled; subscription-only run refuses admission')
    return value


def epoch(value):
    return dt.datetime.fromisoformat(value).timestamp()


def same_window(first, second):
    # The usage helper reconstructs reset timestamps from integer relative times.
    return abs(epoch(first) - epoch(second)) < 60


def admission_allowed(usage, config, now):
    return bool(usage and not STOP.is_set() and now < epoch(config['deadline'])
        and usage['session']['percent_used'] < 98
        and usage['week_all_models']['percent_used'] < 98
        and same_window(usage['week_all_models']['resets'], config['deadline']))


def credentials():
    value = json.loads((Path.home() / '.claude/credentials4.json').read_text())
    if value.get('accountLabel') != 'lean-fro':
        raise RuntimeError('Expected lean-fro credential slot')
    oauth = value['claudeAiOauth']
    if oauth['expiresAt'] / 1000 < time.time() + 60:
        raise RuntimeError('Waiting for the account credential maintainer to refresh lean-fro')
    env = os.environ.copy()
    for key in ['ANTHROPIC_API_KEY', 'ANTHROPIC_AUTH_TOKEN', 'ANTHROPIC_BASE_URL',
                'CLAUDE_CODE_USE_BEDROCK', 'CLAUDE_CODE_USE_VERTEX', 'CLAUDE_CODE_USE_FOUNDRY',
                'CLAUDE_CONFIG_DIR', 'CLAUDECODE']:
        env.pop(key, None)
    env['CLAUDE_CODE_OAUTH_TOKEN'] = oauth['accessToken']
    return env


def sources(row, mode):
    return corpus_pilot.source_dirs(row, mode) if row['lib'] == 'openai-math' else ORIGINAL_DIRS(row, mode)


def existing(audit, sid):
    if sid.startswith('openai-math-'):
        return corpus_pilot.BASE / 'files' / audit / LABEL / 'results' / (sid + '.json')
    label = {'concept-reinvention': LABEL + '-concept',
             'repeated-proof-machinery': LABEL + '-structure-machinery'}.get(audit, LABEL)
    return ROOT / 'runs/file-quality-pilot-2026-10-21' / audit / label / 'results' / (sid + '.json')


def prepare(limit):
    corpus = BASE / 'corpus'
    corpus.mkdir(parents=True, exist_ok=True)
    (corpus / 'libraries.toml').write_text((ROOT / 'libraries.toml').read_text() + '\n' +
        '[[library]]\nid = "openai-math"\nname = "OpenAI Math"\n[[library.source]]\n'
        'dir = "openai-math"\nurl = "https://github.com/openai/math"\ninclude = ["lean/OAI/"]\nexclude = []\n')
    lock = json.loads((ROOT / 'libraries.lock.json').read_text())
    lock['openai-math'] = {'url': 'https://github.com/openai/math', 'commit': corpus_pilot.COMMIT}
    save(corpus / 'libraries.lock.json', lock)
    if not (corpus / 'repos').exists():
        (corpus / 'repos').symlink_to(ROOT / 'repos', target_is_directory=True)
    old_sample, old_files = sample.ROOT, file_audits.ROOT
    sample.ROOT = file_audits.ROOT = corpus
    rows = []
    try:
        # Each library has its own population contract; keep the original SHA256 ordering.
        for lib in LIBRARIES:
            subset, _ = file_audits.prepare(BASE / 'samples' / lib, limit, 0, [lib])
            for row in subset:
                row['file'] = str(Path('samples') / lib / row['file'])
            rows.extend(subset)
    finally:
        sample.ROOT, file_audits.ROOT = old_sample, old_files
    for audit in AUDITS:
        ind = BASE / 'protocols' / audit
        ind.mkdir(parents=True, exist_ok=True)
        for source in (BASE / 'samples/mathlib/protocols' / audit).iterdir():
            target = ind / source.name
            if target.exists() and target.read_bytes() != source.read_bytes():
                raise ValueError('Saved rubric changed')
            target.write_bytes(source.read_bytes())
        out = BASE / audit / LABEL
        (out / 'results').mkdir(parents=True, exist_ok=True)
        protocol = {'backend': 'claude', 'model': 'claude-sonnet-5-5', 'effort': 'high',
                    'audit': audit, 'account_label': 'lean-fro', 'billing': 'subscription_only',
                    'sample_ids': [r['id'] for r in rows if not existing(audit, r['id']).exists()],
                    'artifacts': {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in ind.iterdir()}}
        path = out / 'judge.json'
        if path.exists() and json.loads(path.read_text())['protocol'] != protocol:
            raise ValueError('Saved selection or protocol changed')
        save(path, {'protocol': protocol})
    (BASE / 'samples.jsonl').write_text(''.join(json.dumps(r) + '\n' for r in rows))
    return rows


def process(cmd, message, cwd, timeout):
    """Persist paid output while running and use only this account's OAuth token."""
    with LOCAL.output.open('w') as out, LOCAL.errors.open('w') as err:
        remaining = epoch(json.loads((BASE / 'window.json').read_text())['deadline']) - time.time()
        if remaining <= 0:
            raise RuntimeError('Subscription window ended')
        with subprocess.Popen(cmd, cwd=cwd, env=credentials(), stdin=subprocess.PIPE,
                              stdout=out, stderr=err, text=True, start_new_session=True) as p:
            try:
                p.communicate(message, timeout=min(timeout, remaining))
            except BaseException:
                os.killpg(p.pid, signal.SIGTERM)
                try:
                    p.wait(timeout=10)
                except subprocess.TimeoutExpired:
                    os.killpg(p.pid, signal.SIGKILL)
                    p.wait()
                out.flush(); err.flush()
                LOCAL.attempt_output.write_text(LOCAL.output.read_text())
                LOCAL.attempt_errors.write_text(LOCAL.errors.read_text())
                raise
    return subprocess.CompletedProcess(cmd, p.returncode, LOCAL.output.read_text(), LOCAL.errors.read_text())


def review(row, audit):
    directory = BASE / audit / LABEL / 'results'
    LOCAL.output = directory / (row['id'] + '.live.jsonl')
    LOCAL.errors = directory / (row['id'] + '.live.stderr.log')
    attempt = judge.codex_judge.next_attempt(directory, row['id'])
    LOCAL.attempt_output = directory / f"{row['id']}.attempt-{attempt}.transcript.jsonl"
    LOCAL.attempt_errors = directory / f"{row['id']}.attempt-{attempt}.stderr.log"
    args = argparse.Namespace(backend='claude', model='claude-sonnet-5-5', effort='high',
                             claude='claude', timeout=1200, retries=0, max_budget=5)
    result = file_audits.review(row, audit, BASE, LABEL, args)
    result.update(subscription_account='lean-fro', billing='subscription', actual_api_charge_usd=0)
    save(directory / (row['id'] + '.json'), result)
    (directory / (row['id'] + '.failure.json')).unlink(missing_ok=True)
    return result


def result_for(row, audit):
    local = BASE / audit / LABEL / 'results' / (row['id'] + '.json')
    path = local if local.exists() else existing(audit, row['id'])
    return json.loads(path.read_text()) if path.exists() else None


def report(rows):
    lines = ['# Library quality expansion', '', 'Sonnet 5.5, high effort. Three unchanged rubrics; subscription account lean-fro.',
             'Counts include the existing first pass, without rerunning or charging it again.',
             'Cells are files flagged / reviewed, with Wilson 95% intervals. Flags remain judge claims.', '']
    totals = {}
    for audit in AUDITS:
        lines += ['## ' + audit, '', '| Library | Flagged / reviewed | Rate (95% CI) |', '|---|---:|---:|']
        for lib in LIBRARIES:
            records = [result_for(r, audit) for r in rows if r['lib'] == lib]
            records = [r for r in records if r]
            n = len(records); flags = sum(bool(r['findings']) for r in records)
            lo, hi = wilson(flags, n) if n else (0, 0)
            totals[audit + ':' + lib] = {'completed': n, 'flagged': flags}
            cell = f'{flags/n:.1%} [{lo:.1%}, {hi:.1%}]' if n else '—'
            lines.append(f'| {lib} | {flags}/{n} | {cell} |')
        lines.append('')
    (BASE / 'library-comparison.md').write_text('\n'.join(lines).rstrip() + '\n')
    save(BASE / 'library-comparison.json', totals)
    return totals


def verify_results(rows):
    """Verify saved model output, pinned sources, evidence, tools and billing mode."""
    indexed = {r['id']: r for r in rows}
    counts = Counter()
    for audit in AUDITS:
        ind = BASE / 'protocols' / audit
        for path in (BASE / audit / LABEL / 'results').glob('*.json'):
            if not path.stem.rsplit('-', 1)[-1].isdigit():
                continue
            value = json.loads(path.read_text()); row = indexed[value['id']]
            assert value['model'] == 'claude-sonnet-5-5' and value['effort'] == 'high'
            assert value['subscription_account'] == 'lean-fro' and value['actual_api_charge_usd'] == 0
            text = (BASE / row['file']).read_text()
            assert hashlib.sha256(text.encode()).hexdigest() == row['source_sha256']
            cwd, dirs = sources(row, 'pinned')
            assert hashlib.sha256((cwd / row['path']).read_bytes()).hexdigest() == row['source_sha256']
            file_audits.context.text = text
            file_audits.context.sources = file_audits.Sources([cwd, *dirs.values()])
            keys = json.loads((ind / 'schema.json').read_text())['required']
            verdict = {k: value[k] for k in keys}
            file_audits.validate(verdict, ind)
            raw = json.loads(path.with_name(path.stem + '.raw.json').read_text())
            assert raw['structured_output'] == verdict
            events = [json.loads(x) for x in path.with_name(path.stem + '.transcript.jsonl').read_text().splitlines()]
            initial = next(e for e in events if e.get('type') == 'system' and e.get('subtype') == 'init')
            assert set(initial['tools']) <= {'Read', 'Grep', 'Glob', 'StructuredOutput'}
            assert initial['model'] == 'claude-sonnet-5-5' and initial['apiKeySource'] == 'none'
            for event in events:
                if event.get('type') == 'rate_limit_event':
                    assert not event['rate_limit_info'].get('isUsingOverage', False)
            counts[audit + ':' + row['lib']] += 1
    record = {'checked_utc': dt.datetime.now(dt.timezone.utc).isoformat(),
              'new_accepted': sum(counts.values()), 'new_by_audit_library': dict(counts),
              'billing': 'lean-fro subscription; no API-key authentication or overage observed',
              'checks': ['fixed source hashes', 'source evidence', 'saved structured output',
                         'model and effort', 'read-only tools', 'subscription metadata']}
    save(BASE / 'verification.json', record)
    return record


def refresh_reports():
    for script in ['audit_dashboard.py', 'api_costs.py', 'order_model_tables.py']:
        subprocess.run([os.sys.executable, str(ROOT / 'scripts' / script)], cwd=ROOT,
                       stdout=subprocess.DEVNULL, check=True)


def publish_results(rows):
    verification = verify_results(rows)
    refresh_reports()
    paths = [str(BASE.relative_to(ROOT)), 'AUDIT_RESULTS.md', 'AUDIT_RESULTS.json',
             'runs/main/api-equivalent-costs.md', 'runs/main/api-equivalent-costs.json']
    paths += [str(p.relative_to(ROOT)) for p in (ROOT / 'runs/file-quality-pilot-2026-10-21/reports').glob('*-comparison.*')]
    paths += [str(p.relative_to(ROOT)) for p in (ROOT / 'runs/main').glob('*/audit-comparison.*')]
    subprocess.run(['git', 'add', *paths], cwd=ROOT, check=True)
    if subprocess.run(['git', 'diff', '--cached', '--quiet'], cwd=ROOT).returncode:
        subprocess.run(['git', 'commit', '-m', f"Publish {verification['new_accepted']} subscription-funded library audit judgments"], cwd=ROOT, check=True)
        subprocess.run(['git', 'push', 'origin', 'main'], cwd=ROOT, check=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--prepare', action='store_true')
    parser.add_argument('--limit', type=int, default=1000)
    parser.add_argument('--jobs', type=int, default=8)
    args = parser.parse_args()
    BASE.mkdir(parents=True, exist_ok=True)
    with (BASE / 'controller.lock.log').open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        rows = prepare(args.limit) if args.prepare else [json.loads(x) for x in (BASE / 'samples.jsonl').read_text().splitlines()]
        if args.prepare:
            q = quota()
            save(BASE / 'window.json', {'account': 'lean-fro', 'deadline': q['week_all_models']['resets'],
                 'initial_usage': q, 'jobs': args.jobs, 'admission_gap_seconds': 3, 'audits': AUDITS,
                 'libraries': LIBRARIES, 'maximum_files_per_library': args.limit})
            report(rows)
            return
        judge.judge_dirs = sources
        judge.build_message = file_audits.build_message
        judge.validate_verdict = file_audits.validate
        judge.codex_judge.run_process = process
        (BASE / 'finished.json').unlink(missing_ok=True)
        signal.signal(signal.SIGTERM, lambda *_: STOP.set())
        signal.signal(signal.SIGINT, lambda *_: STOP.set())
        tasks = [(r, a) for r in rows for a in AUDITS if not result_for(r, a)]
        # Round robin over sample index, rubric and library; skip existing judgments.
        tasks.sort(key=lambda t: (int(t[0]['id'].rsplit('-', 1)[1]), AUDITS.index(t[1]), LIBRARIES.index(t[0]['lib'])))
        pending, attempted, failures = {}, set(), []
        attempts = Counter()
        next_quota = next_start = 0
        next_report = 0
        next_dashboard = 0
        next_ramp = time.time() + 180
        rate_limited_until = 0
        q = None
        while tasks or pending:
            config = json.loads((BASE / 'window.json').read_text())
            deadline = epoch(config['deadline'])
            now = time.time()
            if now >= next_quota and not STOP.is_set():
                try:
                    q = quota(); credentials()
                    save(BASE / 'latest-quota.json', {'checked_epoch': now, 'usage': q})
                    next_quota = now + 120
                except Exception as e:
                    q = None; next_quota = now + 60
                    print(json.dumps({'admission_paused': str(e)}), flush=True)
            allowed = admission_allowed(q, config, now)
            allowed &= now >= rate_limited_until
            if allowed and now >= next_ramp and config['jobs'] < config.get('max_jobs', 64) and len(attempted) >= 4:
                config['jobs'] = min(config.get('max_jobs', 64), config['jobs'] + 8)
                save(BASE / 'window.json', config)
                print(json.dumps({'concurrency_increased': config['jobs']}), flush=True)
                next_ramp = now + 180
            if allowed and len(pending) < config['jobs'] and now >= next_start:
                task = next((t for t in tasks if (t[1], t[0]['id']) not in attempted), None)
                if task:
                    r, a = task; attempted.add((a, r['id'])); tasks.remove(task)
                    attempts[a, r['id']] += 1
                    pending[POOL.submit(review, r, a)] = task
                    next_start = now + config.get('admission_gap_seconds', 3)
            done, _ = wait(pending, timeout=3, return_when=FIRST_COMPLETED) if pending else (set(), None)
            for future in done:
                r, a = pending.pop(future)
                try:
                    result = future.result()
                    print(json.dumps({'audit': a, 'id': r['id'], 'verdict': result['verdict']}), flush=True)
                except Exception as e:
                    failure = {'audit': a, 'id': r['id'], 'error': str(e)[:1000]}
                    failures.append(failure)
                    save(BASE / a / LABEL / 'results' / (r['id'] + '.failure.json'), failure)
                    print(json.dumps({'failed': failure}), flush=True)
                    if attempts[a, r['id']] < 3:
                        tasks.insert(0, (r, a)); attempted.discard((a, r['id']))
                    # Rate or quota failures stop new admissions until a fresh quota check.
                    if any(x in str(e).lower() for x in ['rate', 'limit', 'quota', '429']):
                        q = None; next_quota = now + 300
                        rate_limited_until = now + 300
                        next_ramp = now + 1800
                        config['jobs'] = max(1, config['jobs'] // 2)
                        save(BASE / 'window.json', config)
            if now >= next_report or done:
                totals = report(rows)
                next_report = now + 30
                save(BASE / 'status.json', {'checked_utc': dt.datetime.now(dt.timezone.utc).isoformat(),
                 'pid': os.getpid(), 'stage': 'running' if allowed else 'admission-paused',
                 'new_completed': sum(p.stem.rsplit('-', 1)[-1].isdigit() for p in BASE.glob('*/*/results/*.json')),
                 'active': len(pending), 'remaining': len(tasks),
                 'failures': [json.loads(p.read_text()) for p in BASE.glob('*/*/results/*.failure.json')],
                 'failure_history': failures, 'coverage': totals,
                 'deadline': config['deadline'], 'jobs': config['jobs']})
            if now >= next_dashboard:
                refresh_reports()
                next_dashboard = now + 300
            if (STOP.is_set() or now >= deadline or (q and q['week_all_models']['percent_used'] >= 98)) and not pending:
                break
            if not tasks and not pending:
                break
            if not pending:
                time.sleep(5)
        reason = 'stopped' if STOP.is_set() else ('window-ended' if time.time() >= deadline else
                 'weekly-quota-used' if q and q['week_all_models']['percent_used'] >= 98 else 'selected-work-finished')
        save(BASE / 'finished.json', {'utc': dt.datetime.now(dt.timezone.utc).isoformat(), 'reason': reason, 'failures': failures})
        status = json.loads((BASE / 'status.json').read_text())
        status.update(stage=reason, active=0)
        save(BASE / 'status.json', status)
        if not STOP.is_set():
            publish_results(rows)


if __name__ == '__main__':
    with ThreadPoolExecutor(64) as POOL:
        main()
