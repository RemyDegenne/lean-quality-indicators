"""Balanced, source-based Sonnet checks of existing repeated-machinery decisions.

Prepare with --prepare-only, then run with --jobs 2. This does not extend coverage or
overwrite the first pass. The selected 20 positives and 10 negatives per library are
stored independently, excluding the earlier manual-review sample.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED
from collections import Counter
import datetime as dt
import fcntl
import hashlib
import json
import os
from pathlib import Path
import random
import signal
import subprocess
import sys
import threading
import time

import api_costs
import file_audits
import judge
from report import wilson
import subscription_audits as original

ROOT = Path(__file__).resolve().parent.parent
BASE = ROOT / 'runs/repeated-machinery-validation-2026-10-27'
AUDIT = 'repeated-proof-machinery'
LABEL = 'claude-sonnet-5-5-high'
IND = BASE / 'protocols' / AUDIT
OUT = BASE / AUDIT / LABEL
LOCAL = threading.local()
STOP = threading.Event()


def sha(data):
    return hashlib.sha256(data).hexdigest()


def schema():
    finding = json.loads((original.BASE / 'protocols' / AUDIT / 'schema.json').read_text())['properties']['findings']['items']
    evidence = finding['properties']['evidence']
    claim = {'type': 'object', 'properties': {
        'finding_index': {'type': 'integer'},
        'assessment': {'type': 'string', 'enum': ['confirmed', 'refuted', 'uncertain']},
        'reason': {'type': 'string'}, 'shared_lemma': {'type': 'string'},
        'rewritten_uses': {'type': 'array', 'items': {'type': 'string'}, 'maxItems': 5},
        'evidence': {**evidence, 'minItems': 1, 'maxItems': 8}},
        'required': ['finding_index', 'assessment', 'reason', 'shared_lemma', 'rewritten_uses', 'evidence'],
        'additionalProperties': False}
    props = {'coverage': {'type': 'string', 'enum': ['complete', 'partial']},
             'review_notes': {'type': 'string'},
             'claims': {'type': 'array', 'items': claim, 'maxItems': 5},
             'missed_findings': {'type': 'array', 'items': finding, 'maxItems': 5}}
    return {'type': 'object', 'properties': props, 'required': list(props), 'additionalProperties': False}


def select(rows, baseline, excluded, seed='machinery-validation-2026-10-27'):
    selected = []
    for lib in original.LIBRARIES:
        rng = random.Random(seed + ':' + lib)
        for flagged, count in [(True, 20), (False, 10)]:
            pool = sorted([r for r in rows if r['lib'] == lib and r['id'] in baseline
                           and r['id'] not in excluded
                           and bool(baseline[r['id']]['findings']) == flagged], key=lambda r: r['id'])
            if len(pool) < count:
                raise ValueError(f'Insufficient eligible {lib} targets in stratum {flagged}')
            selected.extend({**r, 'baseline_stratum': 'flagged' if flagged else 'unflagged'}
                            for r in rng.sample(pool, count))
    return selected


def prepare():
    BASE.mkdir(parents=True, exist_ok=True)
    path = BASE / 'samples.jsonl'
    if path.exists():
        return [json.loads(s) for s in path.read_text().splitlines()]
    rows = [json.loads(s) for s in (original.BASE / 'samples.jsonl').read_text().splitlines()]
    baseline, paths = {}, {}
    for row in rows:
        p = original.BASE / AUDIT / LABEL / 'results' / (row['id'] + '.json')
        p = p if p.exists() else original.existing(AUDIT, row['id'])
        if p.exists():
            baseline[row['id']] = json.loads(p.read_text()); paths[row['id']] = p
    manual = json.loads((original.BASE / 'sample-review-2026-10-27.json').read_text())
    excluded = {r['target_id'] for r in manual['audits'][AUDIT]['targets']}
    selected = select(rows, baseline, excluded)
    IND.mkdir(parents=True, exist_ok=True)
    prompt = (ROOT / 'audits/repeated-machinery-validation-v1/prompt.md').read_text()
    prompt += '\n\nOriginal rubric:\n\n' + (ROOT / 'audits/file-quality-v1/rubrics' / (AUDIT + '.md')).read_text()
    (IND / 'prompt.md').write_text(prompt)
    original.save(IND / 'schema.json', schema())
    (IND / 'config.toml').write_text('mathlib = "pinned"\n')
    (IND / 'message.md').write_text('Review `{path}` (lines {line}–{end_line}).\n\n'
        'Readable related source directories:\n{dirs}\n\nComplete source:\n```lean\n{snippet}\n```\n\n'
        'Candidate findings to assess (empty means a discovery task):\n{claims}\n')
    for row in selected:
        source = (original.BASE / row['file']).read_bytes()
        assert sha(source) == row['source_sha256']
        destination = BASE / 'files' / (row['id'] + '.lean')
        destination.parent.mkdir(parents=True, exist_ok=True); destination.write_bytes(source)
        row['file'] = str(destination.relative_to(BASE))
        row['baseline_path'] = str(paths[row['id']].relative_to(ROOT))
        row['baseline_sha256'] = sha(paths[row['id']].read_bytes())
        original.save(BASE / 'baseline' / (row['id'] + '.json'), baseline[row['id']])
    # Interleave libraries and strata so partial progress is comparable.
    groups = {lib: [r for r in selected if r['lib'] == lib] for lib in original.LIBRARIES}
    order = [j for i in range(10) for j in (2*i, 2*i+1, 20+i)]
    selected = [groups[lib][i] for i in order for lib in original.LIBRARIES]
    path.write_text(''.join(json.dumps(r) + '\n' for r in selected))
    original.save(BASE / 'selection.json', {
        'seed': 'machinery-validation-2026-10-27', 'flagged_per_library': 20, 'unflagged_per_library': 10,
        'excluded_prior_manual_ids': sorted(excluded),
        'source_population': {lib: {'completed': sum(r['lib'] == lib and r['id'] in baseline for r in rows),
                                  'flagged': sum(bool(baseline[r['id']]['findings']) for r in rows
                                                 if r['lib'] == lib and r['id'] in baseline)}
                              for lib in original.LIBRARIES},
        'purpose': 'Conditional confirmation and missed-finding checks; not another prevalence sample or first pass.'})
    return selected


def validate(value, ind):
    file_audits.check_schema(value, json.loads((ind / 'schema.json').read_text()))
    if not value['review_notes'].strip():
        raise ValueError('Review notes required')
    expected = list(range(len(LOCAL.baseline['findings'])))
    if sorted(c['finding_index'] for c in value['claims']) != expected:
        raise ValueError('Every supplied candidate must be assessed exactly once')
    for claim in value['claims']:
        if not claim['reason'].strip():
            raise ValueError('Claim assessment needs a reason')
        for evidence in claim['evidence']:
            if not Path(evidence['path']).is_absolute():
                raise ValueError('Evidence path must be absolute')
            source = file_audits.context.sources.path(evidence['path']).read_text()
            if not evidence['excerpt'].strip() or file_audits.normalise(evidence['excerpt']) not in file_audits.normalise(source):
                raise ValueError('Evidence quotation absent from cited source')
        if claim['assessment'] == 'confirmed':
            proofs = {(e['path'], e['declaration']) for e in claim['evidence']}
            if len(proofs) < 2 or not claim['shared_lemma'].strip() or len(claim['rewritten_uses']) < 2:
                raise ValueError('Confirmation requires two proofs, a shared lemma and rewritten uses')
            if not all(s.strip() for s in claim['rewritten_uses']):
                raise ValueError('Rewritten uses cannot be empty')
    file_audits.validate({'verdict': 'findings_found' if value['missed_findings'] else 'none_found',
                         'coverage': value['coverage'], 'review_notes': value['review_notes'],
                         'findings': value['missed_findings']}, original.BASE / 'protocols' / AUDIT)


def build_message(row, run, ind, extra=None):
    cwd, dirs, message = file_audits.build_message(row, run, ind, extra)
    return cwd, dirs, message.replace('{claims}', json.dumps(LOCAL.baseline['findings'], indent=2))


def process(cmd, message, cwd, timeout):
    with LOCAL.live.open('w') as out, LOCAL.stderr.open('w') as err:
        remaining = original.epoch(LOCAL.deadline) - time.time()
        if remaining <= 0 or STOP.is_set():
            raise RuntimeError('Validation admission window ended')
        with subprocess.Popen(cmd, cwd=cwd, env=original.credentials(), stdin=subprocess.PIPE,
                              stdout=out, stderr=err, text=True, start_new_session=True) as p:
            try:
                p.communicate(message, timeout=min(timeout, remaining))
            except BaseException:
                os.killpg(p.pid, signal.SIGTERM)
                try:
                    p.wait(timeout=10)
                except subprocess.TimeoutExpired:
                    os.killpg(p.pid, signal.SIGKILL); p.wait()
                out.flush(); err.flush()
                LOCAL.attempt_output.write_text(LOCAL.live.read_text())
                LOCAL.attempt_errors.write_text(LOCAL.stderr.read_text())
                raise
    result = subprocess.CompletedProcess(cmd, p.returncode, LOCAL.live.read_text(), LOCAL.stderr.read_text())
    for line in result.stdout.splitlines():
        try:
            event = json.loads(line)
        except json.JSONDecodeError:
            continue
        if event.get('type') == 'rate_limit_event':
            info = event.get('rate_limit_info', {})
            if info.get('isUsingOverage'):
                STOP.set(); raise RuntimeError('Unexpected overage metadata; admissions stopped')
            if info.get('status') == 'rejected':
                STOP.set(); raise RuntimeError('Rate limit rejected a request; admissions stopped')
    return result


def review(row, deadline):
    LOCAL.baseline = json.loads((BASE / 'baseline' / (row['id'] + '.json')).read_text())
    if sha((ROOT / row['baseline_path']).read_bytes()) != row['baseline_sha256']:
        raise ValueError('Original judgment changed')
    assert sha((BASE / row['file']).read_bytes()) == row['source_sha256']
    cwd, dirs = original.sources(row, 'pinned')
    assert sha((cwd / row['path']).read_bytes()) == row['source_sha256']
    file_audits.context.text = (BASE / row['file']).read_text()
    file_audits.context.sources = file_audits.Sources([cwd, *dirs.values()])
    directory = OUT / 'results'
    attempt = judge.codex_judge.next_attempt(directory, row['id'])
    LOCAL.attempt_output = directory / f"{row['id']}.attempt-{attempt}.transcript.jsonl"
    LOCAL.attempt_errors = directory / f"{row['id']}.attempt-{attempt}.stderr.log"
    # Write straight to retained attempts, so a process/service interruption also
    # preserves paid output for later cost accounting and inspection.
    LOCAL.live, LOCAL.stderr = LOCAL.attempt_output, LOCAL.attempt_errors
    LOCAL.deadline = deadline
    args = argparse.Namespace(backend='claude', model='claude-sonnet-5-5', effort='high',
                             claude='claude', timeout=1200, retries=0, max_budget=2)
    try:
        result = judge.judge_one(row, BASE, IND, directory, args)
        result.update(unit='file_validation', source_sha256=row['source_sha256'],
                      baseline_sha256=row['baseline_sha256'], baseline_stratum=row['baseline_stratum'],
                      subscription_account='lean-fro', billing='subscription', actual_api_charge_usd=0)
        original.save(directory / (row['id'] + '.json'), result)
        return result
    finally:
        del file_audits.context.text, file_audits.context.sources


def disposition(value):
    if value['missed_findings'] or any(c['assessment'] == 'confirmed' for c in value['claims']):
        return 'supported'
    if value['coverage'] == 'partial' or any(c['assessment'] == 'uncertain' for c in value['claims']):
        return 'uncertain'
    return 'unsupported'


def report(rows):
    results = {r['id']: json.loads((OUT / 'results' / (r['id'] + '.json')).read_text()) for r in rows
               if (OUT / 'results' / (r['id'] + '.json')).exists()}
    selection = json.loads((BASE / 'selection.json').read_text())
    data = {'completed': len(results), 'selected': len(rows), 'libraries': {}}
    lines = ['# Repeated proof machinery: validation', '',
             'Sonnet 5.5 high, lean-fro subscription. Twenty flagged and ten unflagged files per library, '
             'excluding the earlier manual sample. Candidate checks try to refute the original findings; '
             'discovery tasks search for missed findings. Results are source-based, not compiled verification. '
             'This is not a new first pass and does not change the main flag rates.', '',
             '| Library | Original flags / reviewed | Flagged checked | Supported | Unsupported | Uncertain | '
             'Unflagged checked | Misses found | API-equivalent USD |',
             '|---|---:|---:|---:|---:|---:|---:|---:|---:|']
    api_costs.DIRECTORY_CACHE.pop(OUT, None)
    for lib in original.LIBRARIES:
        positive = [results[r['id']] for r in rows if r['lib'] == lib and r['id'] in results and r['baseline_stratum'] == 'flagged']
        negative = [results[r['id']] for r in rows if r['lib'] == lib and r['id'] in results and r['baseline_stratum'] == 'unflagged']
        counts = Counter(disposition(v) for v in positive)
        misses = sum(bool(v['missed_findings']) for v in negative)
        cost = api_costs.directory_expenditure(OUT, lib)
        data['libraries'][lib] = {'original': selection['source_population'][lib],
            'flagged_checked': len(positive), 'supported': counts['supported'],
            'unsupported': counts['unsupported'], 'uncertain': counts['uncertain'],
            'supported_fraction_ci95': wilson(counts['supported'], len(positive)) if positive else None,
            'unflagged_checked': len(negative), 'misses': misses,
            'miss_fraction_ci95': wilson(misses, len(negative)) if negative else None,
            'partial_unflagged': sum(v['coverage'] == 'partial' for v in negative), **cost}
        population = selection['source_population'][lib]
        lines.append(f"| {lib} | {population['flagged']}/{population['completed']} | {len(positive)}/20 | "
                     f"{counts['supported']} | {counts['unsupported']} | {counts['uncertain']} | {len(negative)}/10 | "
                     f"{misses} | ${cost['api_usd']:.2f} |")
    lines += ['', 'Supported means at least one supplied claim is confirmed or a new qualifying finding is found. '
              'Unsupported requires all supplied claims refuted and complete coverage; uncertainty is separate. '
              'The JSON report includes Wilson intervals for conditional support and missed-finding fractions. '
              'These measure small-sample uncertainty, not correctness or inter-model agreement.', '',
              'Coverage expansion to 500 files per library remains conditional on reviewing these validation results.']
    original.save(BASE / 'validation-report.json', data)
    (BASE / 'validation-report.md').write_text('\n'.join(lines) + '\n')
    return data


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--prepare-only', action='store_true')
    parser.add_argument('--report-only', action='store_true')
    parser.add_argument('--jobs', type=int, default=2)
    args = parser.parse_args()
    if not 1 <= args.jobs <= 4:
        parser.error('Use one to four sessions')
    rows = prepare(); (OUT / 'results').mkdir(parents=True, exist_ok=True)
    with (BASE / 'controller.lock.log').open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        if args.report_only:
            report(rows); return
        protocol = {'model': 'claude-sonnet-5-5', 'backend': 'claude', 'effort': 'high',
                    'billing': 'subscription_only', 'account': 'lean-fro',
                    'sample_ids': [r['id'] for r in rows],
                    'samples_sha256': sha((BASE / 'samples.jsonl').read_bytes()),
                    'code_sha256': sha(Path(__file__).read_bytes()),
                    'artifacts': {p.name: sha(p.read_bytes()) for p in IND.iterdir()}}
        manifest = OUT / 'judge.json'
        if manifest.exists() and json.loads(manifest.read_text())['protocol'] != protocol:
            raise ValueError('Saved validation protocol changed')
        original.save(manifest, {'protocol': protocol})
        if args.prepare_only:
            report(rows); print(f'Prepared {len(rows)} validation targets'); return
        window = BASE / 'window.json'
        usage = original.quota()
        if not window.exists():
            original.save(window, {'deadline': usage['week_all_models']['resets'], 'initial_usage': usage,
                                   'api_equivalent_ceiling_usd': 50})
        config = json.loads(window.read_text())
        judge.judge_dirs = original.sources
        judge.build_message = build_message
        judge.validate_verdict = validate
        judge.codex_judge.run_process = process
        attempts = Counter(); failures = []; pending = {}; last_quota = time.time(); last_start = 0; last_status = 0
        todo = [r for r in rows if not (OUT / 'results' / (r['id'] + '.json')).exists()]
        stage = 'running'
        with ThreadPoolExecutor(args.jobs) as pool:
            while todo or pending:
                if time.time() - last_quota >= 60:
                    usage = original.quota(); last_quota = time.time()
                allowed = original.admission_allowed(usage, config, time.time()) and not STOP.is_set()
                api_costs.DIRECTORY_CACHE.pop(OUT, None)
                spent = api_costs.directory_expenditure(OUT)['api_usd']
                allowed = allowed and spent + 2 * (len(pending) + 1) <= config['api_equivalent_ceiling_usd']
                if todo and len(pending) < args.jobs and allowed and time.time() - last_start >= 3:
                    row = todo.pop(0); attempts[row['id']] += 1; last_start = time.time()
                    pending[pool.submit(review, row, config['deadline'])] = row
                if not pending and not allowed:
                    stage = 'paused'; break
                finished, _ = wait(pending, timeout=1, return_when=FIRST_COMPLETED) if pending else ([], [])
                for future in finished:
                    row = pending.pop(future)
                    try:
                        value = future.result()
                        print(json.dumps({'id': row['id'], 'result': disposition(value), 'utc': file_audits.utc()}), flush=True)
                    except Exception as exc:
                        failures.append({'id': row['id'], 'error': str(exc), 'utc': file_audits.utc()})
                        print(json.dumps(failures[-1]), flush=True)
                        if attempts[row['id']] < 2 and not STOP.is_set():
                            todo.append(row)
                        else:
                            STOP.set()
                if finished or time.time() - last_status >= 30:
                    data = report(rows)
                    original.save(BASE / 'status.json', {'stage': stage, 'utc': file_audits.utc(),
                        'pid': os.getpid(), 'active': len(pending), 'remaining': len(todo),
                        'completed': data['completed'], 'selected': len(rows), 'failures': failures,
                        'api_equivalent_usd': spent, 'subscription_usage': usage})
                    last_status = time.time()
                if not pending and todo and allowed:
                    time.sleep(1)
        data = report(rows)
        stage = 'complete' if data['completed'] == len(rows) else 'paused'
        original.save(BASE / 'status.json', {'stage': stage, 'utc': file_audits.utc(), 'pid': os.getpid(),
            'completed': data['completed'], 'selected': len(rows), 'active': 0, 'failures': failures})


if __name__ == '__main__':
    main()
