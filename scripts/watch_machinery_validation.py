"""Verify and publish validation progress at most once every five minutes."""
import fcntl
import json
from pathlib import Path
import subprocess
import sys
import time

import api_costs
import file_audits
import validate_repeated_machinery as run


def verify(rows):
    checked = 0
    for row in rows:
        path = run.OUT / 'results' / (row['id'] + '.json')
        if not path.exists():
            continue
        value = json.loads(path.read_text())
        # Ignore the brief interval between judge_one's atomic result write and
        # the runner adding subscription provenance; a later refresh will pick it up.
        if 'subscription_account' not in value:
            continue
        assert value['model'] == 'claude-sonnet-5-5' and value['effort'] == 'high'
        assert value['subscription_account'] == 'lean-fro' and value['actual_api_charge_usd'] == 0
        assert value['source_sha256'] == row['source_sha256']
        assert value['baseline_sha256'] == row['baseline_sha256']
        assert run.sha((run.ROOT / row['baseline_path']).read_bytes()) == row['baseline_sha256']
        text = (run.BASE / row['file']).read_text()
        assert run.sha(text.encode()) == row['source_sha256']
        cwd, dirs = run.original.sources(row, 'pinned')
        assert run.sha((cwd / row['path']).read_bytes()) == row['source_sha256']
        run.LOCAL.baseline = json.loads((run.BASE / 'baseline' / (row['id'] + '.json')).read_text())
        file_audits.context.text = text
        file_audits.context.sources = file_audits.Sources([cwd, *dirs.values()])
        raw = json.loads(path.with_name(path.stem + '.raw.json').read_text())['structured_output']
        run.validate(raw, run.IND)
        assert all(value[k] == v for k, v in raw.items())
        events = [json.loads(s) for s in path.with_name(path.stem + '.transcript.jsonl').read_text().splitlines()]
        initial = next(e for e in events if e.get('type') == 'system' and e.get('subtype') == 'init')
        assert initial['model'] == 'claude-sonnet-5-5' and initial['apiKeySource'] == 'none'
        assert set(initial['tools']) <= {'Read', 'Grep', 'Glob', 'StructuredOutput'}
        for event in events:
            if event.get('type') == 'rate_limit_event':
                assert not event['rate_limit_info'].get('isUsingOverage', False)
        checked += 1
    return checked


def publish(rows):
    with (run.ROOT / 'runs/main/report-publication.lock.log').open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        checked = verify(rows)
        data = run.report(rows)
        if checked != data['completed']:
            return
        run.original.save(run.BASE / 'verification.json', {
            'utc': file_audits.utc(), 'checked': checked,
            'checks': ['fixed target and baseline hashes', 'schema and source evidence',
                       'raw structured output', 'model and effort', 'read-only tools', 'subscription metadata']})
        api_costs.main()
        paths = [str(run.BASE.relative_to(run.ROOT)), 'runs/main/api-equivalent-costs.md',
                 'runs/main/api-equivalent-costs.json']
        already_staged = subprocess.check_output(['git', 'diff', '--cached', '--name-only'],
                                                 cwd=run.ROOT, text=True).splitlines()
        if already_staged:
            raise RuntimeError('Existing staged changes; postpone publication')
        subprocess.run(['git', 'add', '--', *paths], cwd=run.ROOT, check=True)
        staged = subprocess.check_output(['git', 'diff', '--cached', '--name-only'], cwd=run.ROOT, text=True).splitlines()
        # Never commit another session's staged work.
        if any(p not in paths and not p.startswith(paths[0] + '/') for p in staged):
            raise RuntimeError('Unrelated staged changes; postpone publication')
        if staged:
            subprocess.run(['git', 'commit', '-m', f'Publish {checked} verified repeated-machinery validation checks'],
                           cwd=run.ROOT, check=True)
        subprocess.run(['git', 'push', 'origin', 'main'], cwd=run.ROOT, check=True)


def main():
    with (run.BASE / 'monitor.lock.log').open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        rows = [json.loads(s) for s in (run.BASE / 'samples.jsonl').read_text().splitlines()]
        last_completed = -1
        while True:
            status = json.loads((run.BASE / 'status.json').read_text())
            if status['completed'] != last_completed or status['stage'] != 'running':
                publish(rows); last_completed = status['completed']
            if status['stage'] != 'running':
                return
            # The runner has its own 30-second health snapshots and quota/rate-limit
            # controls. This monitor only publishes and makes no inference requests.
            time.sleep(300)


if __name__ == '__main__':
    main()
