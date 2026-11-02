"""Bring OpenAI Math and CFSG Sonnet coverage to parity with the other libraries.

    python3 scripts/sonnet_parity.py prepare [NAME ...]
    python3 scripts/sonnet_parity.py run NAME [--jobs 3] [--max-weekly 90]
    python3 scripts/sonnet_parity.py verify [NAME ...]

Each continuation takes the next targets of a frozen selection and judges them with the
saved prompt, schema, validator and source roots of the earlier Sonnet passes:

- openai-theorems: duplicates-mathlib-inclusive, OpenAI Math theorems 301-1000;
- cfsg-theorems: duplicates-mathlib-inclusive, CFSG theorems 301-1000;
- cfsg-files: repeated-proof-machinery, CFSG files 301-372.

The other libraries have 1000 Sonnet duplicate judgments and 372 repeated-machinery files
each; unnecessary hypotheses is already at 300 everywhere.

Sessions use the Claude Code login of this machine, a Max subscription, not the lean-fro
account of the earlier passes. The runner strips API keys and parent-session variables,
rejects any session that does not report subscription authentication, stops admissions
after a rate-limit rejection or overage event, and stops when the weekly subscription usage
reaches --max-weekly percent. Rerunning `run` resumes; accepted judgments are kept.
"""
import argparse
from collections import Counter
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED
import datetime as dt
import fcntl
import hashlib
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import threading
import time
import urllib.request

import api_costs
import cfsg_pilot
import corpus_pilot
import duplicates_judge
import file_audits
import judge
from source_tools import Sources

ROOT = Path(__file__).resolve().parent.parent
LABEL = 'claude-sonnet-5-5-high'
MODEL = 'claude-sonnet-5-5'
ACCOUNT = 'remy-degenne-max'
CREDENTIALS = Path.home() / '.claude/.credentials.json'
OAI, CFSG = corpus_pilot.BASE, cfsg_pilot.BASE
CODE = ['sonnet_parity.py', 'judge.py', 'codex_judge.py', 'duplicates_judge.py', 'file_audits.py',
        'source_tools.py', 'corpus_pilot.py', 'cfsg_pilot.py', 'sample.py', 'leanscan.py']
STOP = threading.Event()
TOOLS = {'Read', 'Grep', 'Glob', 'StructuredOutput'}


def openai_sources(row, mode='pinned'):
    if row['dir'] != 'openai-math' or mode != 'pinned':
        raise ValueError('Unexpected OpenAI Math source or Mathlib mode')
    head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=corpus_pilot.SOURCE, text=True).strip()
    if head != corpus_pilot.COMMIT:
        raise ValueError('OpenAI Math checkout moved')
    for package in corpus_pilot.dependency_records():
        path = corpus_pilot.dependency_dir(package)
        if subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=path, text=True).strip() != package['rev']:
            raise ValueError('Pinned OpenAI Math dependency moved: ' + str(path))
    return corpus_pilot.source_dirs(row, mode)


def cfsg_sources(row, mode='pinned'):
    if mode != 'pinned':
        raise ValueError('Unexpected Mathlib mode')
    if subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=cfsg_pilot.SOURCE, text=True).strip() != cfsg_pilot.COMMIT:
        raise ValueError('CFSG checkout moved')
    return cfsg_pilot.source_dirs(row, mode)


CONTINUATIONS = {
    'openai-theorems': {'unit': 'theorem', 'audit': 'duplicates-mathlib-inclusive', 'total': 1000,
                        'parent': OAI / 'theorems', 'priors': [OAI / 'theorems', OAI / 'scale-300/theorems'],
                        'base': OAI / 'scale-1000/theorems', 'sources': openai_sources, 'ceiling': 50},
    'cfsg-theorems': {'unit': 'theorem', 'audit': 'duplicates-mathlib-inclusive', 'total': 1000,
                      'parent': CFSG / 'theorems', 'priors': [CFSG / 'theorems', CFSG / 'scale-300/theorems'],
                      'base': CFSG / 'scale-1000/theorems', 'sources': cfsg_sources, 'ceiling': 50},
    'cfsg-files': {'unit': 'file', 'audit': 'repeated-proof-machinery', 'total': 372,
                   'parent': CFSG, 'priors': [CFSG, CFSG / 'scale-300/files'],
                   'base': CFSG / 'scale-372/files', 'sources': cfsg_sources, 'ceiling': 30},
}


def digest(data):
    return hashlib.sha256(data).hexdigest()


def utc():
    return dt.datetime.now(dt.timezone.utc).isoformat(timespec='seconds')


def save(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + f'.{os.getpid()}.tmp')
    temporary.write_text(json.dumps(value, indent=2, ensure_ascii=False) + '\n')
    temporary.replace(path)


def rows(base):
    return [json.loads(s) for s in (base / 'samples.jsonl').read_text().splitlines()]


def results_dir(c):
    return c['base'] / c['audit'] / LABEL / 'results'


def result_for(c, row):
    path = results_dir(c) / (row['id'] + '.json')
    return json.loads(path.read_text()) if path.exists() else None


def prepare(name):
    """Freeze the next targets of the selection and the protocol of the last prior pass."""
    c = CONTINUATIONS[name]
    base, audit = c['base'], c['audit']
    records = rows(c['parent'])
    previous = []
    for prior in c['priors']:
        manifest = prior / audit / LABEL / 'judge.json'
        ids = json.loads(manifest.read_text())['protocol']['sample_ids']
        missing = [s for s in ids if not (manifest.parent / 'results' / (s + '.json')).exists()]
        if missing:
            raise ValueError(f'Prior pass {manifest} is incomplete: {len(missing)} missing')
        previous += ids
    if previous != [r['id'] for r in records[:len(previous)]] or not len(previous) < c['total'] <= len(records):
        raise ValueError('Prior passes are not a prefix of the frozen selection')
    chosen = []
    cwd, _ = c['sources'](records[0])
    for r in records[len(previous):c['total']]:
        snapshot = c['parent'] / r['file']
        row = {**r, 'file': os.path.relpath(snapshot, base)}
        if c['unit'] == 'theorem':
            row['snippet_sha256'] = digest(snapshot.read_bytes())
            row['source_sha256'] = digest((cwd / r['path']).read_bytes())
            if r.get('snippet_sha256', row['snippet_sha256']) != row['snippet_sha256'] or \
                    r.get('source_sha256', row['source_sha256']) != row['source_sha256']:
                raise ValueError('Frozen target changed: ' + r['id'])
        elif digest(snapshot.read_bytes()) != r['source_sha256'] or \
                digest((cwd / r['path']).read_bytes()) != r['source_sha256']:
            raise ValueError('Frozen file changed: ' + r['id'])
        chosen.append(row)
    base.mkdir(parents=True, exist_ok=True)
    text = ''.join(json.dumps(r, ensure_ascii=False) + '\n' for r in chosen)
    samples = base / 'samples.jsonl'
    if samples.exists() and samples.read_text() != text:
        raise ValueError('Continuation targets changed')
    samples.write_text(text)
    last = c['priors'][-1]
    prior_manifest = last / audit / LABEL / 'judge.json'
    original = json.loads(prior_manifest.read_text())['protocol']
    ind = base / 'protocols' / audit
    ind.mkdir(parents=True, exist_ok=True)
    for file, sha in original['artifacts'].items():
        data = (last / 'protocols' / audit / file).read_bytes()
        if digest(data) != sha:
            raise ValueError('Saved rubric changed: ' + file)
        target = ind / file
        if target.exists() and target.read_bytes() != data:
            raise ValueError('Continuation rubric changed')
        target.write_bytes(data)
    if c['unit'] == 'file':
        experiment = json.loads((last / 'experiment.json').read_text())
        save(base / 'experiment.json', {**experiment, 'pilot_files': len(chosen),
             'target_coverage': c['total'], 'baseline_files': len(previous)})
    run_json = last / 'run.json'
    shutil.copyfile(run_json if run_json.exists() else c['parent'] / 'run.json', base / 'run.json')
    protocol = {'backend': 'claude', 'model': MODEL, 'effort': 'high', 'audit': audit, 'unit': c['unit'],
                'account_label': ACCOUNT, 'billing': 'subscription_only',
                'sample_ids': [r['id'] for r in chosen], 'sample_sha256': digest(samples.read_bytes()),
                'selected_population_targets': len(records), 'target_coverage': c['total'],
                'baseline_targets': len(previous), 'artifacts': original['artifacts'],
                'continued_from': [{'manifest': str((p / audit / LABEL / 'judge.json').relative_to(ROOT)),
                                    'sha256': digest((p / audit / LABEL / 'judge.json').read_bytes())}
                                   for p in c['priors']],
                'code_hashes': {f: digest((ROOT / 'scripts' / f).read_bytes()) for f in CODE}}
    manifest = base / audit / LABEL / 'judge.json'
    if manifest.exists():
        # The judge-facing protocol is frozen; runner code changes are recorded, not refused.
        saved = json.loads(manifest.read_text())
        frozen = lambda value: {k: v for k, v in value.items() if k != 'code_hashes'}
        if frozen(saved['protocol']) != frozen(protocol):
            raise ValueError('Saved continuation protocol changed: ' + str(manifest))
        if saved['protocol']['code_hashes'] != protocol['code_hashes']:
            accepted = len([p for p in results_dir(c).glob('*.json') if p.stem.rsplit('-', 1)[-1].isdigit()])
            saved.setdefault('runner_history', []).append({'utc': utc(), 'accepted_before': accepted,
                                                           'code_hashes': saved['protocol']['code_hashes']})
            saved['protocol']['code_hashes'] = protocol['code_hashes']
            save(manifest, saved)
    else:
        version = subprocess.check_output([shutil.which('claude'), '--version'], text=True).strip()
        save(manifest, {'protocol': protocol, 'cli_version': version})
    results_dir(c).mkdir(parents=True, exist_ok=True)
    return chosen


def usage():
    token = json.loads(CREDENTIALS.read_text())['claudeAiOauth']['accessToken']
    request = urllib.request.Request('https://api.anthropic.com/api/oauth/usage', headers={
        'Authorization': 'Bearer ' + token, 'anthropic-beta': 'oauth-2025-04-20'})
    with urllib.request.urlopen(request, timeout=20) as response:
        value = json.load(response)
    return {'checked_utc': utc(), 'weekly_percent': value['seven_day']['utilization'],
            'weekly_resets': value['seven_day']['resets_at'],
            'five_hour_percent': (value.get('five_hour') or {}).get('utilization'),
            'extra_usage_enabled': bool(value.get('extra_usage', {}).get('is_enabled'))}


def session_usage(directory):
    """Fallback: the weekly window reported by the latest judge session's rate-limit event."""
    paths = sorted(directory.glob('*.attempt-*.transcript.jsonl'), key=lambda p: p.stat().st_mtime)
    for path in reversed(paths[-20:]):
        for line in reversed(path.read_text().splitlines()):
            try:
                event = json.loads(line)
            except json.JSONDecodeError:
                continue
            week = event.get('rate_limit_info', {}).get('unifiedWindows', {}).get('seven_day')
            if event.get('type') == 'rate_limit_event' and week:
                return {'checked_utc': utc(), 'source': path.name, 'weekly_percent': round(100 * week['utilization'], 1),
                        'weekly_resets': dt.datetime.fromtimestamp(week['resetsAt'], dt.timezone.utc).isoformat(),
                        'five_hour_percent': None,
                        'extra_usage_enabled': bool(event['rate_limit_info'].get('isUsingOverage'))}
    return None


def environment():
    """The machine's own Claude Code login, without API keys or parent-session links."""
    env = {k: v for k, v in os.environ.items()
           if not (k.startswith('ANTHROPIC_') or k.startswith('CLAUDE'))}
    return env


def process(cmd, message, cwd, timeout):
    if STOP.is_set():
        raise RuntimeError('Admissions stopped')
    with subprocess.Popen(cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                          text=True, cwd=cwd, env=environment(), start_new_session=True) as proc:
        try:
            stdout, stderr = proc.communicate(message, timeout=timeout)
        except BaseException:
            os.killpg(proc.pid, signal.SIGKILL)
            proc.communicate()
            raise
    for line in stdout.splitlines():
        try:
            event = json.loads(line)
        except json.JSONDecodeError:
            continue
        if event.get('type') == 'system' and event.get('subtype') == 'init':
            if event.get('apiKeySource') != 'none':
                STOP.set()
                raise RuntimeError('Session did not use subscription authentication')
            if not set(event.get('tools', [])) <= TOOLS or event.get('model') != MODEL:
                raise RuntimeError('Unexpected tools or model in session')
        if event.get('type') == 'rate_limit_event':
            info = event.get('rate_limit_info', {})
            if info.get('isUsingOverage') or info.get('status') == 'rejected':
                STOP.set()
                raise RuntimeError('Rate limit rejection or overage; admissions stopped')
    return subprocess.CompletedProcess(cmd, proc.returncode, stdout, stderr)


def configure(c):
    judge.judge_dirs = c['sources']
    judge.codex_judge.run_process = process
    if c['unit'] == 'file':
        judge.build_message = file_audits.build_message
        judge.validate_verdict = file_audits.validate
    else:
        judge.build_message = file_audits.original_build_message
        judge.validate_verdict = duplicates_judge.validate


def review(c, row):
    base, audit = c['base'], c['audit']
    args = argparse.Namespace(backend='claude', model=MODEL, effort='high', claude=shutil.which('claude'),
                              timeout=1200, retries=0, max_budget=5)
    if c['unit'] == 'file':
        value = file_audits.review(row, audit, base, LABEL, args)
    else:
        if digest((base / row['file']).read_bytes()) != row['snippet_sha256']:
            raise ValueError('Theorem snapshot changed')
        cwd, _ = c['sources'](row)
        if digest((cwd / row['path']).read_bytes()) != row['source_sha256']:
            raise ValueError('Theorem source changed')
        value = duplicates_judge.judge_one(row, base, base / 'protocols' / audit, results_dir(c), args)
    value.update(subscription_account=ACCOUNT, billing='subscription', actual_api_charge_usd=0)
    save(results_dir(c) / (row['id'] + '.json'), value)
    return value


def run(name, jobs, max_weekly, limit=None):
    c = CONTINUATIONS[name]
    chosen = prepare(name)
    configure(c)
    directory = results_dir(c).parent
    todo = [r for r in chosen if not result_for(c, r)][:limit]
    attempts, failures, active = Counter(), [], {}
    snapshot, checked, attempted, reason = None, 0.0, 0.0, None
    runtime = c['base'] / 'runtime.json'
    if not runtime.exists():
        save(runtime, {'account': ACCOUNT, 'started_utc': utc(), 'initial_usage': usage(),
                       'max_weekly_percent': max_weekly, 'api_equivalent_ceiling_usd': c['ceiling']})

    def status(stage):
        api_costs.DIRECTORY_CACHE.pop(directory, None)
        save(c['base'] / 'status.json', {
            'stage': stage, 'utc': utc(), 'selected': len(chosen),
            'completed': sum(bool(result_for(c, r)) for r in chosen), 'active': len(active),
            'api_equivalent_usd': round(api_costs.directory_expenditure(directory)['api_usd'], 2),
            'failures': failures, 'usage': snapshot, 'stop_reason': reason})

    with ThreadPoolExecutor(jobs) as pool:
        while todo or active:
            # One usage request per five minutes at most, also after a failure (the usage
            # endpoint has its own rate limit). Rejected inference requests stop admissions
            # independently, through the session's rate-limit events.
            if time.time() - attempted > 300:
                attempted = time.time()
                try:
                    snapshot, checked = usage(), time.time()
                except Exception as exc:  # noqa: BLE001
                    fallback = session_usage(results_dir(c))
                    if fallback:
                        snapshot, checked = {**fallback, 'usage_endpoint_error': str(exc)}, time.time()
                    elif snapshot is None or time.time() - checked > 3600:
                        reason = f'usage check failing: {exc}'
                        STOP.set()
            api_costs.DIRECTORY_CACHE.pop(directory, None)
            spent = api_costs.directory_expenditure(directory)['api_usd']
            if snapshot and snapshot['extra_usage_enabled']:
                reason = 'extra usage is enabled'; STOP.set()
            elif snapshot and snapshot['weekly_percent'] >= max_weekly:
                reason = f"weekly usage {snapshot['weekly_percent']}% >= {max_weekly}%"; STOP.set()
            elif spent + 2 > c['ceiling']:
                reason = f'API-equivalent ceiling ${c["ceiling"]} reached'; STOP.set()
            five = snapshot and snapshot['five_hour_percent']
            while todo and len(active) < jobs and not STOP.is_set() and not (five and five >= 95):
                row = todo.pop(0)
                attempts[row['id']] += 1
                active[pool.submit(review, c, row)] = row
                time.sleep(2)
            if not active:
                if STOP.is_set() or not todo:
                    break
                status('waiting for the five-hour window')
                time.sleep(300)
                attempted = 0
                continue
            done, _ = wait(list(active), timeout=60, return_when=FIRST_COMPLETED)
            for future in done:
                row = active.pop(future)
                try:
                    value = future.result()
                    print(json.dumps({'utc': utc(), 'id': row['id'], 'verdict': value['verdict']}), flush=True)
                except Exception as exc:  # noqa: BLE001
                    failure = {'id': row['id'], 'attempt': attempts[row['id']], 'error': str(exc)[:500], 'utc': utc()}
                    failures.append(failure)
                    print(json.dumps(failure), flush=True)
                    if attempts[row['id']] < 3:
                        todo.append(row)
            status('running')
    complete = all(result_for(c, r) for r in chosen)
    status('complete' if complete else 'paused')
    print(json.dumps({'continuation': name, 'complete': complete, 'reason': reason}), flush=True)


def verify(name):
    """Check every accepted judgment against its saved output, sources and billing mode."""
    c = CONTINUATIONS[name]
    base, audit = c['base'], c['audit']
    configure(c)
    protocol = json.loads((base / audit / LABEL / 'judge.json').read_text())['protocol']
    chosen = rows(base)
    assert protocol['sample_ids'] == [r['id'] for r in chosen]
    assert protocol['sample_sha256'] == digest((base / 'samples.jsonl').read_bytes())
    for entry in protocol['continued_from']:
        assert digest((ROOT / entry['manifest']).read_bytes()) == entry['sha256']
    ind = base / 'protocols' / audit
    for file, sha in protocol['artifacts'].items():
        assert digest((ind / file).read_bytes()) == sha
    changed = [f for f, sha in protocol['code_hashes'].items() if digest((ROOT / 'scripts' / f).read_bytes()) != sha]
    keys = json.loads((ind / 'schema.json').read_text())['required']
    cwd, dirs = c['sources'](chosen[0])
    count = 0
    for row in chosen:
        value = result_for(c, row)
        if not value:
            continue
        assert value['model'] == MODEL and value['effort'] == 'high'
        assert value['subscription_account'] == ACCOUNT and value['actual_api_charge_usd'] == 0
        verdict = {k: value[k] for k in keys}
        if c['unit'] == 'file':
            text = (base / row['file']).read_text()
            assert digest(text.encode()) == row['source_sha256']
            assert digest((cwd / row['path']).read_bytes()) == row['source_sha256']
            file_audits.context.text = text
            file_audits.context.sources = Sources([cwd, *dirs.values()])
            file_audits.validate(verdict, ind)
        else:
            assert digest((base / row['file']).read_bytes()) == row['snippet_sha256']
            assert digest((cwd / row['path']).read_bytes()) == row['source_sha256']
            duplicates_judge.context.sample = row
            duplicates_judge.validate(verdict, ind)
        directory = results_dir(c)
        raw = json.loads((directory / (row['id'] + '.raw.json')).read_text())
        assert raw['structured_output'] == verdict
        events = [json.loads(s) for s in (directory / (row['id'] + '.transcript.jsonl')).read_text().splitlines()]
        initial = next(e for e in events if e.get('type') == 'system' and e.get('subtype') == 'init')
        assert set(initial['tools']) <= TOOLS and initial['model'] == MODEL and initial['apiKeySource'] == 'none'
        assert not any(e.get('rate_limit_info', {}).get('isUsingOverage') for e in events
                       if e.get('type') == 'rate_limit_event')
        count += 1
    flagged = Counter(r['verdict'] for r in map(lambda r: result_for(c, r), chosen) if r)
    result = {'checked_utc': utc(), 'accepted': count, 'selected': len(chosen), 'verdicts': dict(flagged),
              'code_changed_since_preparation': changed,
              'checks': ['frozen selection, protocol and prior manifests', 'source and snapshot hashes',
                         'schema and audit validators', 'raw structured output', 'read-only tools',
                         'subscription authentication, no overage']}
    save(base / 'verification.json', result)
    print(json.dumps({'continuation': name, **result}), flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    parser.add_argument('command', choices=['prepare', 'run', 'verify'])
    parser.add_argument('names', nargs='*', help=', '.join(CONTINUATIONS))
    parser.add_argument('--jobs', type=int, default=3)
    parser.add_argument('--max-weekly', type=float, default=90)
    parser.add_argument('--limit', type=int, help='judge at most this many new targets (trial runs)')
    args = parser.parse_args()
    names = args.names or list(CONTINUATIONS)
    if set(names) - set(CONTINUATIONS):
        parser.error('unknown continuation: ' + ', '.join(sorted(set(names) - set(CONTINUATIONS))))
    if args.command == 'run':
        if len(names) != 1:
            parser.error('run takes exactly one continuation')
        base = CONTINUATIONS[names[0]]['base']
        base.mkdir(parents=True, exist_ok=True)
        with (base / 'controller.lock.log').open('a') as lock:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
            run(names[0], args.jobs, args.max_weekly, args.limit)
        return
    for name in names:
        if args.command == 'prepare':
            print(name, len(prepare(name)), 'targets')
        else:
            verify(name)


if __name__ == '__main__':
    main()
