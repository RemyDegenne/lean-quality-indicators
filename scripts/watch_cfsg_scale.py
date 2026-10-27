"""Publish verified CFSG coverage at 300 targets per audit; no inference requests."""
import fcntl
import json
import subprocess
import sys
import time

import cfsg_scale as scale


def publish():
    with (scale.ROOT / 'runs/main/report-publication.lock.log').open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        for unit in ('file', 'theorem'):
            subprocess.run([sys.executable, str(scale.ROOT / 'scripts/cfsg_scale.py'), unit, '--report-only'],
                           cwd=scale.ROOT, check=True)
        totals = scale.summary()
        scale.runner.refresh_reports()
        paths = [str(scale.BASE.relative_to(scale.ROOT)), 'AUDIT_RESULTS.md', 'AUDIT_RESULTS.json',
                 'AUDIT_APPENDIX.md', 'runs/main/api-equivalent-costs.md', 'runs/main/api-equivalent-costs.json']
        paths += [str(p.relative_to(scale.ROOT)) for p in
                  (scale.ROOT / 'runs/file-quality-pilot-2026-10-21/reports').glob('*-comparison.*')]
        paths += [str(p.relative_to(scale.ROOT)) for p in (scale.ROOT / 'runs/main').glob('*/audit-comparison.*')]
        paths += [str(p.relative_to(scale.ROOT)) for p in
                  (scale.ROOT / 'runs/defs1/definition-fidelity').glob('audit-comparison.*')]
        if subprocess.check_output(['git', 'diff', '--cached', '--name-only'], cwd=scale.ROOT, text=True).strip():
            raise RuntimeError('Existing staged work; defer publication')
        subprocess.run(['git', 'add', '--', *paths], cwd=scale.ROOT, check=True)
        staged = subprocess.check_output(['git', 'diff', '--cached', '--name-only'], cwd=scale.ROOT, text=True).splitlines()
        if any(p not in paths and not p.startswith(paths[0] + '/') for p in staged):
            raise RuntimeError('Unrelated staged changes; defer publication')
        if staged:
            count = sum(t['completed'] for t in totals.values())
            subprocess.run(['git', 'commit', '-m', f'Publish expanded CFSG coverage: {count}/900 judgments'],
                           cwd=scale.ROOT, check=True)
        subprocess.run(['git', 'push', 'origin', 'main'], cwd=scale.ROOT, check=True)


def main():
    with (scale.BASE / 'monitor.lock.log').open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        previous = None
        while True:
            states = []
            for unit in ('file', 'theorem'):
                path = scale.destination(unit) / 'status.json'
                states.append(json.loads(path.read_text()) if path.exists() else {'stage': 'starting', 'completed': 0})
            current = [(s['stage'], s['completed']) for s in states]
            if current != previous:
                publish()
                previous = current
            if all(s['stage'] in ('complete', 'paused') for s in states):
                return
            time.sleep(300)


if __name__ == '__main__':
    main()
