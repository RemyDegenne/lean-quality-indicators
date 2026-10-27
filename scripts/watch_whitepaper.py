"""Wait for complete Sonnet continuations, then refresh and publish the whitepaper."""
import argparse
import datetime
import fcntl
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parent.parent
REPORT = ROOT / 'reports/formalization-quality-whitepaper.md'
STATE = ROOT / 'runs/main/whitepaper-publication.json'
RUNS = [ROOT / 'runs/cfsg-pilot-2026-10-27/scale-300/files',
        ROOT / 'runs/cfsg-pilot-2026-10-27/scale-300/theorems',
        ROOT / 'runs/openai-math-2026-10-21/scale-300/theorems']
REPORTS = ['runs/main/unnecessary-hypotheses/audit-comparison.json',
           'runs/main/duplicates-mathlib-inclusive/audit-comparison.json',
           'runs/file-quality-pilot-2026-10-21/reports/repeated-proof-machinery-comparison.json']
LIBRARIES = {'Mathlib': 'mathlib', 'Tau Ceti': 'tauceti', 'Formal Frontier': 'formal-frontier',
             'Lean Pool': 'lean-pool', 'Anthropic FLT': 'flt-anthropic',
             'OpenAI Math': 'openai-math', 'AxiomMath CFSG': 'axiom-cfsg'}


def digest(data):
    return hashlib.sha256(data).hexdigest()


def save(value):
    temporary = STATE.with_suffix('.tmp')
    temporary.write_text(json.dumps(value, indent=2) + '\n')
    temporary.replace(STATE)


def progress():
    groups = {}
    ready = True
    for base in RUNS:
        manifests = sorted(base.glob('*/*/judge.json'))
        if not manifests:
            ready = False
        for manifest in manifests:
            selected = json.loads(manifest.read_text())['protocol']['sample_ids']
            completed = sum((manifest.parent / 'results' / (sid + '.json')).exists() for sid in selected)
            groups[str(manifest.parent.relative_to(ROOT))] = {'completed': completed, 'selected': len(selected)}
            ready &= completed == len(selected)
    return ready, groups


def updated_markdown(text, data):
    parts = text.split('\n## ')
    if len(parts) != 4:
        raise ValueError('Whitepaper section structure changed; preserve text for manual review')
    for index, report in enumerate(data, 1):
        lines = parts[index].splitlines()
        found = 0
        for number, line in enumerate(lines):
            if not line.startswith('|'):
                continue
            cells = [c.strip() for c in line.strip().strip('|').split('|')]
            lib = LIBRARIES.get(cells[0])
            if lib is None:
                continue
            if len(cells) != (2 if index == 3 else 3):
                raise ValueError('Whitepaper model columns changed')
            model = report['groups'][lib]['models']['Sonnet']
            first = model['passes'][0]
            n, flagged = first['completed'], first['flagged']
            if not n:
                raise ValueError('Expected completed Sonnet sample')
            lo, hi = model['first_pass_rate_ci95']
            cells[-1] = f'{flagged:,}/{n:,} · **{flagged/n:.1%}** [{lo:.1%}, {hi:.1%}]'
            lines[number] = '| ' + ' | '.join(cells) + ' |'
            found += 1
        if found != (6 if index == 2 else 7):
            raise ValueError('Unexpected library rows')
        parts[index] = '\n'.join(lines)
    text = '\n## '.join(parts).rstrip() + '\n'
    coverage = ('Sonnet now covers 300 theorems per audit for both OpenAI Math and CFSG, '
                '300 CFSG files, and 372 OpenAI Math files.')
    text, changed = re.subn(r'CFSG figures use its completed 30-target pilots(?:; an expansion to 300 targets per audit is running)?\.',
                           coverage, text)
    if not changed and coverage not in text:
        raise ValueError('Coverage text changed; preserve text for manual review')
    text = text.replace('/blob/b235c6613/', '/blob/main/')
    return text


def publish():
    with (ROOT / 'runs/main/report-publication.lock.log').open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        ready, counts = progress()
        if not ready:
            return False
        if subprocess.check_output(['git', 'diff', '--cached', '--name-only'], cwd=ROOT, text=True).strip():
            raise RuntimeError('Existing staged work; defer publication')
        for command in [['cfsg_scale.py', 'file', '--report-only'], ['cfsg_scale.py', 'theorem', '--report-only'],
                        ['openai_scale.py', '--report-only'], ['audit_dashboard.py'], ['api_costs.py'], ['order_model_tables.py']]:
            subprocess.run([sys.executable, str(ROOT / 'scripts' / command[0]), *command[1:]],
                           cwd=ROOT, check=True, stdout=subprocess.DEVNULL)
        import cfsg_scale
        cfsg_scale.summary()
        source = REPORT.read_bytes()
        data = [json.loads((ROOT / path).read_text()) for path in REPORTS]
        updated = updated_markdown(source.decode(), data)
        with tempfile.TemporaryDirectory(prefix='whitepaper-final-') as temporary:
            directory = Path(temporary)
            md = directory / REPORT.name
            pdf = md.with_suffix('.pdf')
            md.write_text(updated)
            subprocess.run([sys.executable, str(ROOT / 'scripts/render_whitepaper.py'), str(md), str(pdf)],
                           cwd=ROOT, check=True)
            if REPORT.read_bytes() != source:
                raise RuntimeError('Markdown edited during rendering; retry with latest wording')
            REPORT.write_text(updated)
            REPORT.with_suffix('.pdf').write_bytes(pdf.read_bytes())
        save({'stage': 'ready-to-push', 'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
              'runs': counts, 'markdown_sha256': digest(REPORT.read_bytes()),
              'pdf_sha256': digest(REPORT.with_suffix('.pdf').read_bytes()), 'pages': 2})
        paths = [str(REPORT.relative_to(ROOT)), str(REPORT.with_suffix('.pdf').relative_to(ROOT)),
                 str(STATE.relative_to(ROOT)), 'AUDIT_RESULTS.md', 'AUDIT_RESULTS.json', 'AUDIT_APPENDIX.md',
                 'runs/main/api-equivalent-costs.md', 'runs/main/api-equivalent-costs.json',
                 'runs/cfsg-pilot-2026-10-27/scale-300', 'runs/openai-math-2026-10-21/scale-300']
        paths += [str(p.relative_to(ROOT)) for p in (ROOT / 'runs/main').glob('*/audit-comparison.*')]
        paths += [str(p.relative_to(ROOT)) for p in (ROOT / 'runs/defs1/definition-fidelity').glob('audit-comparison.*')]
        paths += [str(p.relative_to(ROOT)) for p in (ROOT / 'runs/file-quality-pilot-2026-10-21/reports').glob('*-comparison.*')]
        subprocess.run(['git', 'add', '--', *paths], cwd=ROOT, check=True)
        staged = subprocess.check_output(['git', 'diff', '--cached', '--name-only'], cwd=ROOT, text=True).splitlines()
        allowed_trees = [p for p in paths if p.endswith('/scale-300')]
        if any(p not in paths and not any(p.startswith(prefix + '/') for prefix in allowed_trees) for p in staged):
            raise RuntimeError('Unrelated staged files; defer publication')
        subprocess.run(['git', 'diff', '--cached', '--check'], cwd=ROOT, check=True)
        if staged:
            subprocess.run(['git', 'commit', '-m', 'Refresh whitepaper and PDF with completed Sonnet expansions'], cwd=ROOT, check=True)
        subprocess.run(['git', 'push', 'origin', 'main'], cwd=ROOT, check=True)
        receipt = json.loads(STATE.read_text())
        receipt.update(stage='published', published_commit=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip())
        # Local receipt avoids another commit solely to record its own commit hash.
        (STATE.parent / 'whitepaper-published.log').write_text(json.dumps(receipt, indent=2) + '\n')
        print(json.dumps(receipt), flush=True)
        return True


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check-only', action='store_true')
    args = parser.parse_args()
    with (ROOT / 'runs/main/whitepaper-monitor.lock.log').open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        while True:
            ready, counts = progress()
            print(json.dumps({'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
                              'ready': ready, 'runs': counts}), flush=True)
            if args.check_only:
                return
            if ready and publish():
                return
            time.sleep(60)


if __name__ == '__main__':
    main()
