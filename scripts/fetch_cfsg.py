"""Fetch pinned CFSG Lean sources and dependencies without certificate payloads."""
import subprocess

import cfsg_pilot as pilot
import fetch


def main():
    source = pilot.SOURCE
    source.mkdir(parents=True, exist_ok=True)
    if not (source / '.git').exists():
        subprocess.run(['git', 'init', '-q'], cwd=source, check=True)
        subprocess.run(['git', 'remote', 'add', 'origin', 'https://github.com/AxiomMath/CFSG.git'],
                       cwd=source, check=True)
    head = subprocess.run(['git', 'rev-parse', '--verify', 'HEAD'], cwd=source, text=True, capture_output=True)
    if head.returncode == 0 and head.stdout.strip() != pilot.COMMIT:
        raise RuntimeError('Existing CFSG checkout has moved; use an isolated pinned checkout')
    subprocess.run(['git', 'config', 'remote.origin.promisor', 'true'], cwd=source, check=True)
    subprocess.run(['git', 'config', 'remote.origin.partialclonefilter', 'blob:none'], cwd=source, check=True)
    if head.returncode:
        subprocess.run(['git', 'fetch', '--depth', '1', '--filter=blob:none', 'origin', pilot.COMMIT],
                       cwd=source, check=True)
    subprocess.run(['git', 'sparse-checkout', 'init', '--no-cone'], cwd=source, check=True)
    subprocess.run(['git', 'sparse-checkout', 'set', '--no-cone', '--stdin'], cwd=source, check=True,
                   input='/*\n!/*/\n/CFSG/\n/Comparator/\n/Certificates/**/*.lean\n', text=True)
    subprocess.run(['git', 'checkout', '--detach', pilot.COMMIT], cwd=source, check=True)
    for package in pilot.dependencies():
        fetch.fetch_dep(package['name'].strip('«»'), package['url'], package['rev'])
    pilot.source_dirs({'dir': 'axiom-cfsg'})


if __name__ == '__main__':
    main()
