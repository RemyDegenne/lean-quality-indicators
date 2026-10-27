"""Verify and publish CFSG pilot snapshots, with no inference requests."""
import fcntl
import json
import subprocess
import time

import cfsg_pilot as pilot


def publish(rows):
    with (pilot.ROOT / 'runs/main/report-publication.lock.log').open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        pilot.verify(rows)
        pilot.report(rows)
        pilot.runner.refresh_reports()
        paths = [str(pilot.BASE.relative_to(pilot.ROOT)), 'AUDIT_RESULTS.md', 'AUDIT_RESULTS.json', 'AUDIT_APPENDIX.md',
                 'runs/main/api-equivalent-costs.md', 'runs/main/api-equivalent-costs.json']
        paths += [str(p.relative_to(pilot.ROOT)) for p in (pilot.ROOT / 'runs/file-quality-pilot-2026-10-21/reports').glob('*-comparison.*')]
        paths += [str(p.relative_to(pilot.ROOT)) for p in (pilot.ROOT / 'runs/main').glob('*/audit-comparison.*')]
        paths += [str(p.relative_to(pilot.ROOT)) for p in (pilot.ROOT / 'runs/defs1/definition-fidelity').glob('audit-comparison.*')]
        if subprocess.check_output(['git', 'diff', '--cached', '--name-only'], cwd=pilot.ROOT, text=True).strip():
            raise RuntimeError('Existing staged work; defer publication')
        subprocess.run(['git', 'add', '--', *paths], cwd=pilot.ROOT, check=True)
        staged = subprocess.check_output(['git', 'diff', '--cached', '--name-only'], cwd=pilot.ROOT, text=True).splitlines()
        if any(p not in paths and not p.startswith(paths[0] + '/') for p in staged):
            raise RuntimeError('Unrelated staged changes; defer publication')
        if staged:
            count = sum(bool(pilot.runner.result_for(row, pilot.AUDIT)) for row in rows)
            subprocess.run(['git', 'commit', '-m', f'Publish {count} source-verified CFSG pilot judgments'],
                           cwd=pilot.ROOT, check=True)
        subprocess.run(['git', 'push', 'origin', 'main'], cwd=pilot.ROOT, check=True)


def main():
    pilot.configure()
    with (pilot.BASE / 'monitor.lock.log').open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        rows = [json.loads(s) for s in (pilot.BASE / 'samples.jsonl').read_text().splitlines()]
        selected = set(json.loads((pilot.BASE / pilot.AUDIT / pilot.LABEL / 'judge.json').read_text())['protocol']['sample_ids'])
        rows = [r for r in rows if r['id'] in selected]
        previous = -1
        while True:
            status = json.loads((pilot.BASE / 'status.json').read_text())
            if status['completed'] != previous or status['stage'] != 'running':
                publish(rows); previous = status['completed']
            if status['stage'] != 'running':
                return
            time.sleep(300)


if __name__ == '__main__':
    main()
