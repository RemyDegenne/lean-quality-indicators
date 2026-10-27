"""Run existing frozen Sonnet continuations with shared quota checks and pacing."""
import argparse
from concurrent.futures import ProcessPoolExecutor, wait, FIRST_COMPLETED
import fcntl
import hashlib
import json
import multiprocessing
from pathlib import Path
import re
import subprocess
import sys
import time

import api_costs
import subscription_audits as runner

ROOT = Path(__file__).resolve().parent.parent
CONTROL = ROOT / 'data/sonnet-scale-control'
JOBS = 2
SPACING = 5
QUOTA_TTL = 300


def quota():
    """Serialize fresh quota requests and retry without admitting new inference."""
    CONTROL.mkdir(parents=True, exist_ok=True)
    with (CONTROL / 'quota.lock').open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        cache = CONTROL / 'quota.json'
        if cache.exists():
            saved = json.loads(cache.read_text())
            if time.time() - saved['checked_epoch'] < QUOTA_TTL:
                return saved['usage']
        for attempt in range(3):
            result = subprocess.run([str(runner.USAGE), '--account', 'lean-fro', '--ttl', str(QUOTA_TTL),
                                     '--no-stale'], capture_output=True, text=True, timeout=45)
            if result.returncode == 0:
                try:
                    value = json.loads(result.stdout)
                    for field in ('session', 'week_all_models'):
                        if not isinstance(value[field]['percent_used'], (int, float)):
                            raise ValueError('Missing quota percentage')
                    if value.get('extra_usage', {}).get('is_enabled'):
                        raise RuntimeError('Extra usage enabled; refusing subscription-only admission')
                    runner.save(cache, {'checked_epoch': time.time(), 'usage': value})
                    return value
                except (ValueError, KeyError, TypeError):
                    pass
            print(json.dumps({'event': 'quota-check-unavailable', 'attempt': attempt + 1,
                              'admission': 'waiting'}), flush=True)
            if attempt < 2:
                time.sleep(15)
    raise RuntimeError('Fresh quota unavailable; no new inference admitted')


def paced_process(original, cmd, message, cwd, timeout):
    CONTROL.mkdir(parents=True, exist_ok=True)
    with (CONTROL / 'starts.lock').open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        if (CONTROL / 'rate-limit-stop.json').exists():
            raise RuntimeError('Shared rate-limit stop is set')
        path = CONTROL / 'last-start.json'
        previous = json.loads(path.read_text())['epoch'] if path.exists() else 0
        time.sleep(max(0, previous + SPACING - time.time()))
        runner.save(path, {'epoch': time.time()})
    result = original(cmd, message, cwd, timeout)
    rejected = bool(re.search(r'rate_limit_error|too many requests|(?:HTTP\S*\s+|status(?:_code)?[=: ]+)429\b',
                              result.stdout + result.stderr, re.I))
    for line in result.stdout.splitlines():
        try:
            event = json.loads(line)
        except json.JSONDecodeError:
            continue
        if event.get('type') == 'rate_limit_event':
            info = event.get('rate_limit_info', {})
            rejected |= bool(info.get('isUsingOverage') or info.get('status') == 'rejected')
    if rejected:
        runner.LOCAL.attempt_output.write_text(result.stdout)
        runner.LOCAL.attempt_errors.write_text(result.stderr)
        runner.save(CONTROL / 'rate-limit-stop.json', {'epoch': time.time(), 'reason': 'inference rate limit or overage rejection'})
        raise RuntimeError('Inference rejection; shared admission stopped')
    return result


def configure(kind):
    if kind == 'openai':
        import openai_scale as adapter
        adapter.configure()
        module = adapter.engine
    else:
        import cfsg_scale as adapter
        module = adapter.configure('file' if kind == 'cfsg-files' else 'theorem')
    runner.quota = quota
    import judge
    # Keep the saved judge invocation, source handling and validators unchanged.
    original = module.corpus.ORIGINAL_PROCESS if kind != 'cfsg-files' else module.ORIGINAL_PROCESS
    judge.codex_judge.run_process = lambda *args: paced_process(original, *args)
    return module


def review(kind, row, audit):
    module = configure(kind)
    return runner.review(row, audit) if kind == 'cfsg-files' else module.review(row, audit)


def should_run(kind):
    """Allow recovery after credential/quota failures, but never restart finished work or a rate stop."""
    if (CONTROL / 'rate-limit-stop.json').exists():
        return False
    module = configure(kind)
    base = module.BASE
    config = json.loads((base / 'window.json').read_text())
    if time.time() >= runner.epoch(config['deadline']):
        return False
    todo = False
    for manifest in base.glob('*/*/judge.json'):
        protocol = json.loads(manifest.read_text())['protocol']
        for sid in protocol['sample_ids']:
            directory = manifest.parent / 'results'
            if (directory / (sid + '.json')).exists():
                continue
            todo = True
            import judge
            if judge.codex_judge.next_attempt(directory, sid) > 3:
                return False
            failure = directory / (sid + '.failure.json')
            if failure.exists():
                error = json.loads(failure.read_text())['error']
                if 'OAuth token revoked' not in error and not error.startswith('Invalid verdict:'):
                    return False
    return todo


def run(kind):
    module = configure(kind)
    base = module.BASE
    chosen = [json.loads(s) for s in (base / 'samples.jsonl').read_text().splitlines()]
    audits = [module.AUDIT] if kind == 'cfsg-files' else module.AUDITS
    config = json.loads((base / 'window.json').read_text())
    label = module.LABEL
    def result(row, audit):
        path = base / audit / label / 'results' / (row['id'] + '.json')
        return path.exists()
    todo = [(row, audit) for row in chosen for audit in audits if not result(row, audit)]
    failures = []
    usage = None
    pending = {}
    note = ''
    baseline_completed = len(chosen) * len(audits) - len(todo)
    runner.save(base / 'runtime-control.json', {'controller': 'scripts/sonnet_scale_control.py',
        'sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(), 'jobs': JOBS,
        'global_start_spacing_seconds': SPACING, 'shared_quota_ttl_seconds': QUOTA_TTL,
        'started_epoch': time.time(), 'completed_on_start': baseline_completed,
        'protocol': 'Existing frozen selections, prompts, model, effort, authentication and validators unchanged'})
    def status(stage):
        totals = module.report(chosen)
        for audit in audits:
            directory = base / audit / label
            api_costs.DIRECTORY_CACHE.pop(directory, None)
        completed = sum(result(row, audit) for row in chosen for audit in audits)
        runner.save(base / 'status.json', {'stage': stage, 'utc': __import__('datetime').datetime.now(
            __import__('datetime').timezone.utc).isoformat(), 'completed': completed,
            'selected': len(chosen) * len(audits), 'active': len(pending), 'jobs': JOBS,
            'by_audit': totals, 'failures': failures, 'subscription_usage': usage, 'admission_note': note})
    with (base / 'controller.lock.log').open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        with ProcessPoolExecutor(JOBS, mp_context=multiprocessing.get_context('spawn')) as pool:
            last_status = 0
            while todo or pending:
                allowed = False
                if todo and len(pending) < JOBS and not runner.STOP.is_set():
                    try:
                        usage = quota()
                        allowed = runner.admission_allowed(usage, config, time.time())
                        note = '' if allowed else 'Quota, deadline or subscription-window guard'
                    except (RuntimeError, subprocess.TimeoutExpired) as exc:
                        note = str(exc)
                if (CONTROL / 'rate-limit-stop.json').exists():
                    allowed = False
                    runner.STOP.set()
                    note = 'Shared inference rate-limit stop'
                while allowed and todo and len(pending) < JOBS:
                    for audit in audits:
                        api_costs.DIRECTORY_CACHE.pop(base / audit / label, None)
                    spent = sum(api_costs.directory_expenditure(base / audit / label)['api_usd'] for audit in audits)
                    if spent + (len(pending) + 1) * 5 > config['api_equivalent_ceiling_usd']:
                        note = 'API-equivalent ceiling reserve'
                        allowed = False
                        break
                    row, audit = todo.pop(0)
                    if result(row, audit):
                        continue
                    import judge
                    attempts = judge.codex_judge.next_attempt(base / audit / label / 'results', row['id'])
                    if attempts > 3:
                        note = 'Target exhausted retained attempts'
                        runner.STOP.set()
                        break
                    pending[pool.submit(review, kind, row, audit)] = (row, audit)
                done, _ = wait(pending, timeout=10, return_when=FIRST_COMPLETED) if pending else (set(), set())
                for future in done:
                    row, audit = pending.pop(future)
                    try:
                        value = future.result()
                        print(json.dumps({'audit': audit, 'id': row['id'], 'verdict': value['verdict']}), flush=True)
                    except Exception as exc:
                        failure = {'audit': audit, 'id': row['id'], 'error': str(exc)}
                        failures.append(failure)
                        runner.save(base / audit / label / 'results' / (row['id'] + '.failure.json'), failure)
                        note = str(exc)
                        import judge
                        attempts = judge.codex_judge.next_attempt(base / audit / label / 'results', row['id'])
                        retryable = 'OAuth token revoked' in str(exc) or str(exc).startswith('Invalid verdict:')
                        if retryable and attempts <= 3 and not (CONTROL / 'rate-limit-stop.json').exists():
                            todo.append((row, audit))
                        else:
                            runner.STOP.set()
                if time.time() - last_status >= 30:
                    status('running')
                    last_status = time.time()
                if not pending and (runner.STOP.is_set() or not allowed):
                    if note.startswith('Fresh quota unavailable') and not runner.STOP.is_set():
                        status('running')
                        time.sleep(30)
                        continue
                    break
        module.verify(chosen)
        complete = all(result(row, audit) for row in chosen for audit in audits)
        status('complete' if complete else 'paused')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('kind', choices=['cfsg-files', 'cfsg-theorems', 'openai'])
    parser.add_argument('--should-run', action='store_true')
    args = parser.parse_args()
    if args.should_run:
        sys.exit(0 if should_run(args.kind) else 1)
    run(args.kind)
