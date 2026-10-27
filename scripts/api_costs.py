"""Estimate retained audit costs at a frozen set of API token rates."""

from collections import defaultdict
import datetime
import json
from pathlib import Path

from file_audits import RUBRICS
from audit_reporting import is_main_audit, reporting_status

ROOT = Path(__file__).resolve().parent.parent
MAIN = ROOT / "runs/main"
FILES = ROOT / "runs/file-quality-pilot-2026-10-21"

RATES = json.loads((ROOT / "pricing/api-rates-2026-10-21.json").read_text())
DIRECTORY_CACHE = {}


def token_cost(result):
    if result.get("backend") == "openrouter":
        return result.get("cost_usd"), "billed API cost"
    rates = RATES["models"].get(result.get("model"))
    usage = result.get("usage")
    if not usage or not rates:
        return result.get("cost_usd"), "reported API equivalent"
    if result.get("backend") == "codex":
        cached = usage.get("cached_input_tokens", 0)
        writes = usage.get("cache_write_input_tokens", 0)
        total = max(0, usage.get("input_tokens", 0) - cached - writes) * rates["input"] + cached * rates["cached_input"] + writes * rates["cache_write"] + usage.get("output_tokens", 0) * rates["output"]
    else:
        writes = usage.get("cache_creation_input_tokens", 0)
        hour = usage.get("cache_creation", {}).get("ephemeral_1h_input_tokens", 0)
        total = usage.get("input_tokens", 0) * rates["input"] + usage.get("cache_read_input_tokens", 0) * rates["cached_input"] + max(0, writes - hour) * rates["cache_write"] + hour * rates.get("cache_write_1h", rates["cache_write"]) + usage.get("output_tokens", 0) * rates["output"]
    return total / 1_000_000, "token estimate"


def directory_expenditure(directory, lib=None):
    """Accepted judgments plus separately retained rejected/interrupted attempts."""
    directory = Path(directory)
    if directory not in DIRECTORY_CACHE:
        buckets = defaultdict(lambda: {"api_usd": 0., "retry_api_usd": 0., "uncosted_attempts": 0})
        results = {p.stem: json.loads(p.read_text()) for p in (directory / "results").glob("*.json")
                   if p.stem.rsplit("-", 1)[-1].isdigit()}
        for result in results.values():
            amount, _ = token_cost(result)
            if amount is not None:
                buckets[result["lib"]]["api_usd"] += amount
        manifest = directory / "judge.json"
        protocol = json.loads(manifest.read_text()).get("protocol", {}) if manifest.exists() else {}
        model = protocol.get("model") or next(iter(results.values()), {}).get("model")
        backend = protocol.get("backend") or next(iter(results.values()), {}).get("backend")
        for transcript in (directory / "results").glob("*.attempt-*.transcript.jsonl"):
            sid, attempt = transcript.name.split(".attempt-", 1)
            attempt = int(attempt.split(".", 1)[0])
            if sid in results and attempt == results[sid].get("attempts", 1):
                continue  # Already costed from the accepted judgment.
            usage, reported = None, None
            billed_events = []
            for line in transcript.read_text().splitlines():
                try:
                    event = json.loads(line)
                except json.JSONDecodeError:
                    continue
                if event.get("type") == "api_response":
                    cost = event.get("response", {}).get("usage", {}).get("cost")
                    if cost is not None:
                        billed_events.append(float(cost))
                if event.get("type") in ["turn.completed", "result"]:
                    usage = event.get("usage")
                    reported = event.get("total_cost_usd", event.get("cost_usd"))
            if backend == "openrouter" and billed_events:
                reported = sum(billed_events)
            library = results.get(sid, {}).get("lib") or (
                sid.split("-file-", 1)[0] if "-file-" in sid else sid.rsplit("-", 1)[0])
            amount, _ = token_cost({"model": model, "backend": backend, "usage": usage, "cost_usd": reported})
            if amount is not None:
                buckets[library]["api_usd"] += amount
                buckets[library]["retry_api_usd"] += amount
            else:
                buckets[library]["uncosted_attempts"] += 1
        DIRECTORY_CACHE[directory] = dict(buckets)
    buckets = DIRECTORY_CACHE[directory]
    selected = [buckets.get(lib, {})] if lib else list(buckets.values())
    return {key: sum(row.get(key, 0) for row in selected)
            for key in ["api_usd", "retry_api_usd", "uncosted_attempts"]}


def full_pass_estimate(expenditure, completed, largest_pass):
    return expenditure / completed * largest_pass if completed else None


def main():
    groups = defaultdict(lambda: {"completed": 0, "api_usd": 0., "costed": 0, "reported_only": 0})
    largest_pass = defaultdict(int)
    model_names = {"gpt-6.1-sol": "Sol", "gpt-6-luna": "Luna", "claude-sonnet-5-5": "Sonnet",
                   "claude-opus-5-5": "Opus", "deepseek/deepseek-v4.1-flash-1017": "DeepSeek"}
    selected = []
    for audit in ["unnecessary-hypotheses", "duplicates-mathlib-inclusive", "duplicates-mathlib"]:
        for directory in (MAIN / audit).iterdir():
            if directory.is_dir() and not directory.name.startswith("pilot"):
                selected.append((audit, directory))
    for audit in RUBRICS:
        selected += [(audit, d) for d in (FILES / audit).iterdir() if d.is_dir()]
    extra = ROOT / "runs/openai-math-2026-10-21"
    for unit in ("theorems", "files"):
        selected += [(manifest.parent.parent.name, manifest.parent)
                     for manifest in (extra / unit).glob("*/*/judge.json")]
    expansion = ROOT / 'runs/library-quality-scale-2026-10-26'
    selected += [(manifest.parent.parent.name, manifest.parent)
                 for manifest in expansion.glob('*/*/judge.json')]
    cfsg = ROOT / 'runs/cfsg-pilot-2026-10-27'
    selected += [(manifest.parent.parent.name, manifest.parent)
                 for manifest in cfsg.glob('*/*/judge.json')]
    selected += [(manifest.parent.parent.name, manifest.parent)
                 for manifest in (cfsg / 'theorems').glob('*/*/judge.json')]
    for unit in ('files', 'theorems'):
        selected += [(manifest.parent.parent.name, manifest.parent)
                     for manifest in (cfsg / 'scale-300' / unit).glob('*/*/judge.json')]
    selected.append(('definition-fidelity', ROOT / 'runs/defs1/definition-fidelity/claude-opus-5-5-high'))
    validation = ROOT / 'runs/repeated-machinery-validation-2026-10-27/repeated-proof-machinery/claude-sonnet-5-5-high'
    if (validation / 'judge.json').exists():
        selected.append(('repeated-proof-machinery-validation', validation))
        largest_pass['repeated-proof-machinery-validation'] = len(
            json.loads((validation / 'judge.json').read_text())['protocol']['sample_ids'])
    for source_audit, directory in selected:
        audit = "duplicates-mathlib-inclusive" if source_audit == "duplicates-mathlib" else source_audit
        directory_completed = 0
        for p in (directory / "results").glob("*.json"):
            if not p.stem.rsplit("-", 1)[-1].isdigit():
                continue
            result = json.loads(p.read_text())
            directory_completed += 1
            name = model_names.get(result.get("model"), result.get("model", "unknown"))
            if audit == 'definition-fidelity' and name == 'rule':
                name = 'Opus'  # Same composite protocol; missing-docstring flags incur no inference cost.
            row = groups[audit, name]
            row["completed"] += 1
            amount, method = token_cost(result)
            if amount is not None:
                row["costed"] += 1
                row["api_usd"] += amount
                row["reported_only"] += method == "reported API equivalent"
        largest_pass[audit] = max(largest_pass[audit], directory_completed)
        # Include available retry usage in recorded expenditure, not just successes.
        results_model = next(iter((directory / "results").glob("*.json")), None)
        manifest = directory / "judge.json"
        model = json.loads(manifest.read_text()).get("protocol", {}).get("model") if manifest.exists() else None
        if model is None and results_model:
            model = json.loads(results_model.read_text()).get("model")
        if model:
            name = model_names.get(model, model)
            if audit == 'definition-fidelity' and name == 'rule':
                name = 'Opus'
            row = groups[audit, name]
            expenditure = directory_expenditure(directory)
            row["api_usd"] += expenditure["retry_api_usd"]
            row["retry_api_usd"] = row.get("retry_api_usd", 0) + expenditure["retry_api_usd"]
            row["uncosted_attempts"] = row.get("uncosted_attempts", 0) + expenditure["uncosted_attempts"]
    for audit in largest_pass:
        report = (ROOT / 'runs/defs1/definition-fidelity/audit-comparison.json' if audit == 'definition-fidelity'
                  else FILES / "reports" / f"{audit}-comparison.json" if audit in RUBRICS
                  else MAIN / audit / "audit-comparison.json")
        if report.exists():
            largest_pass[audit] = json.loads(report.read_text())["groups"]["all"]["full_pass_reference_targets"]
    table_header = ["| Audit | Model | Accepted judgments | Full-pass targets | API expenditure / full-pass estimate | USD / 1,000 judgments |",
                    "|---|---|---:|---:|---:|---:|"]
    lines = ["# API-equivalent costs", "",
             f"Generated {datetime.datetime.now(datetime.timezone.utc).isoformat(timespec='seconds')} · "
             "[Methods and notation](../../AUDIT_METHODS.md).", "",
             *table_header]
    lines[4:4] = ['Definition fidelity groups automatic missing-docstring flags with its Opus protocol; '
                  'rule-only decisions cost $0. Repeated-machinery validation is a separate check, '
                  'excluded from the original first-pass judgment and coverage counts.', '']
    totals = defaultdict(float)
    order = {name: i for i, name in enumerate(["Opus", "Sol", "Sonnet", "Luna", "DeepSeek"])}
    audits = {audit: i for i, audit in enumerate(dict.fromkeys(audit for audit, _ in groups))}
    appendix_started = False
    for (audit, model), row in sorted(groups.items(), key=lambda item: (
            not is_main_audit(item[0][0]), audits[item[0][0]], order.get(item[0][1], 99))):
        if not is_main_audit(audit) and not appendix_started:
            lines += ["", "## Appendix audits: not ready for use", "",
                      "[Assessment](../../AUDIT_APPENDIX.md). Excluded from the main report aggregates; "
                      "their recorded expenditure remains part of the totals below.", "", *table_header]
            appendix_started = True
        cost = row["api_usd"]
        totals[model] += cost
        unit = cost / row["costed"] * 1000 if row["costed"] else 0
        full = full_pass_estimate(cost, row["completed"], largest_pass[audit])
        row["full_pass_reference_targets"] = largest_pass[audit]
        row["full_pass_estimate_usd"] = full
        row["reporting_status"] = reporting_status(audit)
        money = f"${cost:.2f} / ${full:.2f}" if full is not None else f"${cost:.2f} / —"
        lines.append(f"| {audit} | {model} | {row['completed']} | {largest_pass[audit]} | {money} | ${unit:.2f} |")
    lines += ["", "## Totals by model", "", "| Model | API-equivalent USD |", "|---|---:|"]
    for model, amount in totals.items():
        lines.append(f"| {model} | ${amount:.2f} |")
    lines += [f"| **Total** | **${sum(totals.values()):.2f}** |"]
    lines += ["", "## Rate sources", "", *[f"- [{url}]({url})" for url in RATES["sources"]], "",
              "Frozen rates: `pricing/api-rates-2026-10-21.json`. Refresh with `python3 scripts/api_costs.py`. "
              "Mean-based projections include recorded retry expenditure and will change as more targets complete."]
    (MAIN / "api-equivalent-costs.md").write_text("\n".join(lines) + "\n")
    data = {"generated_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(timespec='seconds'),
            "rates": RATES, "rows": [{"audit": a, "model": m, **r} for (a, m), r in groups.items()],
            "totals_by_model": dict(totals)}
    (MAIN / "api-equivalent-costs.json").write_text(json.dumps(data, indent=2) + "\n")
    print(json.dumps(data["totals_by_model"]))


if __name__ == "__main__":
    main()
