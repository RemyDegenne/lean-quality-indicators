"""Estimate retained audit costs at a frozen set of API token rates."""

from collections import defaultdict
import datetime
import json
from pathlib import Path

from file_audits import RUBRICS

ROOT = Path(__file__).resolve().parent.parent
MAIN = ROOT / "runs/main"
FILES = ROOT / "runs/file-quality-pilot-2026-10-21"

RATES = json.loads((ROOT / "pricing/api-rates-2026-10-21.json").read_text())
DIRECTORY_CACHE = {}


def token_cost(result):
    rates = RATES["models"].get(result.get("model"))
    usage = result.get("usage")
    if not usage or not rates:
        return result.get("cost_usd"), "reported API equivalent"
    if isinstance(usage, list):
        # Pi uses mutually exclusive input and cache-read counts. Output includes reasoning.
        total = sum(u.get("input", 0) * rates["input"] + u.get("cacheRead", 0) * rates["cached_input"] +
                    u.get("cacheWrite", 0) * rates["cache_write"] + u.get("output", 0) * rates["output"] for u in usage)
    elif result.get("backend") == "codex":
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
            # These bootstrap calls were saved separately before their paths were reused.
            if model == "z-ai/glm-5.3" and directory.parent.name == "unnecessary-hypotheses" and sid == "mathlib-0000" and attempt in (2, 3):
                continue
            usage, reported = None, None
            messages = []
            for line in transcript.read_text().splitlines():
                try:
                    event = json.loads(line)
                except json.JSONDecodeError:
                    continue
                if event.get("type") in ["turn.completed", "result", "judge_result"]:
                    usage = event.get("usage")
                    reported = event.get("total_cost_usd", event.get("cost_usd"))
                if event.get("type") == "message_end" and event.get("message", {}).get("role") == "assistant":
                    messages.append(event["message"].get("usage", {}))
            if usage is None and backend == "pi" and messages:
                usage = messages
            library = results.get(sid, {}).get("lib") or (
                sid.split("-file-", 1)[0] if "-file-" in sid else sid.rsplit("-", 1)[0])
            amount, _ = token_cost({"model": model, "backend": backend, "usage": usage, "cost_usd": reported})
            if amount is not None:
                buckets[library]["api_usd"] += amount
                buckets[library]["retry_api_usd"] += amount
            else:
                buckets[library]["uncosted_attempts"] += 1
        setup = MAIN / "pi-glm-pilot/setup-usage.json"
        if directory.name == "glm-5.3-openrouter-pi-high-pilot" and directory.parent.name == "unnecessary-hypotheses" and setup.exists():
            amount, _ = token_cost({"model": "z-ai/glm-5.3", "usage": json.loads(setup.read_text())["usage"]})
            buckets["mathlib"]["api_usd"] += amount
            buckets["mathlib"]["retry_api_usd"] += amount
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
                   "claude-opus-5-5": "Opus", "z-ai/glm-5.3": "GLM"}
    selected = []
    for audit in ["unnecessary-hypotheses", "duplicates-mathlib-inclusive", "duplicates-mathlib"]:
        for directory in (MAIN / audit).iterdir():
            if directory.is_dir() and not directory.name.startswith("pilot"):
                selected.append((audit, directory))
    for audit in RUBRICS:
        selected += [(audit, d) for d in (FILES / audit).iterdir() if d.is_dir()]
    for source_audit, directory in selected:
        audit = "duplicates-mathlib-inclusive" if source_audit == "duplicates-mathlib" else source_audit
        directory_completed = 0
        for p in (directory / "results").glob("*.json"):
            if not p.stem.rsplit("-", 1)[-1].isdigit():
                continue
            result = json.loads(p.read_text())
            directory_completed += 1
            name = model_names.get(result.get("model"), result.get("model", "unknown"))
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
            row = groups[audit, name]
            expenditure = directory_expenditure(directory)
            row["api_usd"] += expenditure["retry_api_usd"]
            row["retry_api_usd"] = row.get("retry_api_usd", 0) + expenditure["retry_api_usd"]
            row["uncosted_attempts"] = row.get("uncosted_attempts", 0) + expenditure["uncosted_attempts"]
    lines = ["# API-equivalent costs", "",
             f"Generated {datetime.datetime.now(datetime.timezone.utc).isoformat(timespec='seconds')}. All amounts USD.", "",
             "Standard short-context API rates, including recorded cache hits/writes and reasoning output. "
             "These are API-equivalent estimates, not subscription charges. GLM is repriced at the frozen OpenRouter model-list rates, "
             "which can differ from provider-specific routing prices and the pi SDK's bundled price list. "
             "Opus baseline token counts were not retained, so its saved API-equivalent dollar amounts are used.", "",
             "Counts below cover accepted judgments of the eight current audits and the original Opus duplicate baseline. "
             "Expenditure also includes separately retained retry/interrupted-call usage. "
             "Deleted experiments, this coordinating conversation, and failed calls whose usage was not saved cannot be reconstructed. "
             "They therefore do not reconstruct the entire historical bill.", "",
             "Each $X / $Y cell shows recorded expenditure / estimated cost of a single pass at the "
             "largest observed pass for that audit. Y uses the model's expenditure per accepted judgment, including retained retries. "
             "The reference target count is shown explicitly. Opus duplication is the original four-library baseline, "
             "extrapolated to the five-library reference scale.", "",
             "| Audit | Model | Accepted judgments | Full-pass targets | API expenditure / full-pass estimate | USD / 1,000 judgments |",
             "|---|---|---:|---:|---:|---:|"]
    totals = defaultdict(float)
    for (audit, model), row in groups.items():
        cost = row["api_usd"]
        totals[model] += cost
        unit = cost / row["costed"] * 1000 if row["costed"] else 0
        full = full_pass_estimate(cost, row["completed"], largest_pass[audit])
        row["full_pass_reference_targets"] = largest_pass[audit]
        row["full_pass_estimate_usd"] = full
        money = f"${cost:.2f} / ${full:.2f}" if full is not None else f"${cost:.2f} / —"
        lines.append(f"| {audit} | {model} | {row['completed']} | {largest_pass[audit]} | {money} | ${unit:.2f} |")
    lines += ["", "## Totals by model", "", "| Model | API-equivalent USD |", "|---|---:|"]
    for model, amount in totals.items():
        lines.append(f"| {model} | ${amount:.2f} |")
    lines += [f"| **Total** | **${sum(totals.values()):.2f}** |", "", "## GLM projection", "",
              "Pilot means are early estimates; theorem and whole-file audits are projected separately.", "",
              "| Audit | Accepted GLM judgments | Observed API equivalent | Planned judgments | Projected accepted-judgment cost |",
              "|---|---:|---:|---:|---:|"]
    for audit in ["unnecessary-hypotheses", "duplicates-mathlib-inclusive", *RUBRICS]:
        row = groups.get((audit, "GLM"), {"completed": 0, "costed": 0, "api_usd": 0})
        planned = 30 if audit in RUBRICS else 50
        estimate = f"${row['api_usd']/row['costed']*planned:.2f}" if row["costed"] else "Awaiting first accepted judgment"
        lines.append(f"| {audit} | {row['completed']} | ${row['api_usd']:.3f} | {planned} | {estimate} |")
    setup = MAIN / "pi-glm-pilot/setup-usage.json"
    overhead = 0
    if setup.exists():
        overhead, _ = token_cost({"model": "z-ai/glm-5.3", "usage": json.loads(setup.read_text())["usage"]})
        lines += ["", f"Included in GLM hypothesis expenditure: initial parser-rejected setup calls, ${overhead:.4f} API equivalent."]
    lines += ["", "## Rate sources", "", *[f"- [{url}]({url})" for url in RATES["sources"]], "",
              "Frozen rates: `pricing/api-rates-2026-10-21.json`. Refresh with `python3 scripts/api_costs.py`. "
              "Mean-based projections include recorded retry expenditure and will change as more targets complete."]
    (MAIN / "api-equivalent-costs.md").write_text("\n".join(lines) + "\n")
    data = {"generated_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(timespec='seconds'),
            "rates": RATES, "rows": [{"audit": a, "model": m, **r} for (a, m), r in groups.items()],
            "totals_by_model": dict(totals), "recorded_glm_setup_usd": overhead}
    (MAIN / "api-equivalent-costs.json").write_text(json.dumps(data, indent=2) + "\n")
    print(json.dumps(data["totals_by_model"]))


if __name__ == "__main__":
    main()
