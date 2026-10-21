"""Coverage, flag rates and matched-target correlation reports for all current audits."""

import argparse
import datetime
import hashlib
import json
import math
from pathlib import Path
import random
import tomllib

from report import wilson
from api_costs import directory_expenditure, full_pass_estimate

ROOT = Path(__file__).resolve().parent.parent
FILES = ROOT / "runs/file-quality-pilot-2026-10-21"
MAIN = ROOT / "runs/main"
RUBRICS = ["concept-reinvention", "statement-generality", "vacuity-and-misstatement",
           "simp-interface", "repeated-proof-machinery", "readable-proof-simplification"]
LABELS = {"Sol": ["gpt-6.1-sol-high", "gpt-6.1-sol-high-repeat-2"],
          "Sonnet": ["claude-sonnet-5-5-high", "claude-sonnet-5-5-high-repeat-2"],
          "Luna": ["gpt-6-luna-high", "gpt-6-luna-high-repeat-2"],
          "GLM": ["glm-5.3-openrouter-pi-high-pilot"]}


def load(directory):
    return {p.stem: json.loads(p.read_text()) for p in (directory / "results").glob("*.json")
            if p.stem.rsplit("-", 1)[-1].isdigit()}


def phi(counts):
    a, b, c, d = counts  # 00, 01, 10, 11
    denominator = (a + b) * (c + d) * (a + c) * (b + d)
    return (a * d - b * c) / math.sqrt(denominator) if denominator else None


def multinomial(counts, rng):
    remaining = sum(counts)
    population = remaining
    draw = []
    for count in counts[:-1]:
        number = rng.binomialvariate(remaining, count / population) if population else 0
        draw.append(number)
        remaining -= number
        population -= count
    return [*draw, remaining]


def correlation(first, second, samples, positive, seed, resamples):
    ids = sorted(first.keys() & second.keys() & samples.keys())
    strata = {}
    for i in ids:
        group = strata.setdefault(samples[i]["lib"], [0] * 4)
        group[2 * positive(first[i]) + positive(second[i])] += 1
    counts = [sum(g[j] for g in strata.values()) for j in range(4)]
    r = phi(counts)
    result = {"n": len(ids), "r": r, "ci95": None, "counts_00_01_10_11": counts,
              "matched_ids_sha256": hashlib.sha256("\n".join(ids).encode()).hexdigest()}
    if r is None or abs(r) >= 1 or len(ids) < 4:
        result["interval_note"] = "constant input, boundary estimate, or fewer than four targets"
        return result
    rng = random.Random(seed)
    estimates = []
    for _ in range(resamples):
        draw = [0] * 4
        for group in strata.values():
            for j, number in enumerate(multinomial(group, rng)):
                draw[j] += number
        estimate = phi(draw)
        if estimate is not None:
            estimates.append(estimate)
    result["degenerate_resamples"] = resamples - len(estimates)
    # Do not silently discard a material number of undefined bootstrap correlations.
    if len(estimates) >= math.ceil(0.975 * resamples):
        estimates.sort()
        result["ci95"] = [estimates[int(0.025 * (len(estimates) - 1))],
                          estimates[int(0.975 * (len(estimates) - 1))]]
    else:
        result["interval_note"] = "more than 2.5% of resamples have constant inputs"
    return result


def models_for(audit, base, samples, is_file):
    models = {}
    labels = {k: v[:] for k, v in LABELS.items()}
    if is_file:
        labels.pop("Sol")
        labels["Luna"] = labels["Luna"][:1]
        labels["Sonnet"] = [{"concept-reinvention": "claude-sonnet-5-5-high-concept",
                              "repeated-proof-machinery": "claude-sonnet-5-5-high-structure-machinery"}.get(audit, "claude-sonnet-5-5-high")]
        labels["GLM"] = ["glm-5.3-openrouter-pi-high"]
    else:
        labels = {"Opus": ["claude-opus-5-5-high", "rejudge-claude-opus-5-5-high"], **labels}
        if audit == "duplicates-mathlib-inclusive":
            labels = {k: v[:1] for k, v in labels.items()}
    for name, passes in labels.items():
        records = []
        for index, label in enumerate(passes):
            directory = base / label
            if name == "Opus" and audit == "duplicates-mathlib-inclusive":
                directory = MAIN / "duplicates-mathlib" / label
            rows = load(directory)
            manifest = directory / "judge.json"
            if manifest.exists():
                info = json.loads(manifest.read_text())
                selected = info.get("sample_ids") or info.get("protocol", {}).get("sample_ids")
                if selected is None and info.get("selections"):
                    selected = info["selections"][-1]["sample_ids"]
            else:
                selected = None
            if selected is None:
                if is_file:
                    selected = list(samples)
                else:
                    limit = 10 if name == "GLM" else 1000 if audit.startswith("duplicates") else 400 if name == "Opus" and index == 0 else 300
                    selected = [i for i, s in samples.items() if int(i.rsplit("-", 1)[1]) < limit
                                and not (name == "Opus" and audit.startswith("duplicates") and s["lib"] == "mathlib")]
            records.append({"label": label, "directory": directory, "selected": set(selected), "results": rows})
        models[name] = records
    return models


def library_table(data, libraries, names):
    models = data["groups"]["all"]["models"]
    lines = ["| Library | " + " | ".join(models) + " |", "|---|" + "---:|" * len(models)]
    for lib in libraries:
        cells = []
        for model in models:
            row = data["groups"][lib]["models"][model]
            first = row["passes"][0]
            n, flags = first["completed"], first["flagged"]
            if not n:
                cells.append("—")
                continue
            lo, hi = row["first_pass_rate_ci95"]
            cells.append(f"{flags}/{n}<br>{flags/n:.1%} [{lo:.1%}, {hi:.1%}]")
        lines.append(f"| {names[lib]} | " + " | ".join(cells) + " |")
    return lines


def make_report(audit, base, samples, is_file, resamples):
    models = models_for(audit, base, samples, is_file)
    positive = (lambda r: bool(r.get("findings"))) if is_file else (
        lambda r: r["verdict"] in (["duplicate", "special_case"] if audit.startswith("duplicates") else ["unnecessary_hypothesis_found"]))
    names = {lib["id"]: lib["name"] for lib in tomllib.loads((ROOT / "libraries.toml").read_text())["library"]}
    libraries = [lib for lib in names if any(s["lib"] == lib for s in samples.values())]
    data = {"audit": audit, "unit": "file" if is_file else "theorem", "groups": {}}
    methods = "../../../AUDIT_METHODS.md"
    lines = [f"# {audit}", "", f"Generated {datetime.datetime.now(datetime.timezone.utc).isoformat(timespec='seconds')} · "
             f"[Methods and notation]({methods}) · {resamples:,} bootstrap draws.", ""]
    if audit == "duplicates-mathlib-inclusive":
        lines += ["Opus uses the earlier prompt on four libraries, without Mathlib targets.", ""]
    if audit == "unnecessary-hypotheses":
        lines += ["Opus: 400 then 300 targets/library; Sol, Sonnet and Luna: 300 per pass.", ""]
    for lib, title in [(None, "All libraries"), *[(lib, names[lib]) for lib in libraries]]:
        scoped = {i: s for i, s in samples.items() if lib is None or s["lib"] == lib}
        group = {"models": {}, "correlations": {}}
        completed_sizes = [len(entry["selected"] & scoped.keys()) for passes in models.values() for entry in passes
                           if entry["selected"] & scoped.keys() and
                           entry["selected"] & scoped.keys() <= entry["results"].keys()]
        largest = max(completed_sizes, default=0)
        group["full_pass_reference_targets"] = largest
        lines += [f"## {title}", "", f"Full-pass reference: **{largest} targets**.", "",
                  "| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |",
                  "|---|---:|---:|---:|---:|---:|---:|---:|"]
        for name, passes in models.items():
            selected, flagged_ids = set(), set()
            completed = expected = flags = finished = partial = na = 0
            per_pass = []
            for entry in passes:
                ids = entry["selected"] & scoped.keys()
                rows = {i: r for i, r in entry["results"].items() if i in ids}
                marked = {i for i, r in rows.items() if positive(r)}
                selected |= ids
                flagged_ids |= marked
                completed += len(rows)
                expected += len(ids)
                flags += len(marked)
                finished += bool(ids) and len(rows) == len(ids)
                partial += sum(r.get("coverage") == "partial" for r in rows.values())
                na += sum(r.get("verdict") == "not_applicable" for r in rows.values())
                per_pass.append({"selected": len(ids), "completed": len(rows), "flagged": len(marked)})
            first = per_pass[0]
            lo, hi = wilson(first["flagged"], first["completed"]) if first["completed"] else (None, None)
            rate = f"{first['flagged']/first['completed']:.1%} [{lo:.1%}, {hi:.1%}]" if first["completed"] else "—"
            costs = [directory_expenditure(entry["directory"], lib) for entry in passes]
            expenditure = sum(c["api_usd"] for c in costs)
            estimate = full_pass_estimate(expenditure, completed, largest)
            money = f"${expenditure:.2f} / ${estimate:.2f}" if estimate is not None else f"${expenditure:.2f} / —"
            group["models"][name] = {"selected_targets": len(selected), "passes_completed": finished,
                "passes_planned": len(passes), "judgments_completed": completed, "judgments_planned": expected,
                "flagged_judgments": flags, "distinct_targets_flagged": len(flagged_ids), "passes": per_pass,
                "first_pass_rate_ci95": [lo, hi], "partial_reviews": partial, "not_applicable_reviews": na,
                "api_expenditure_usd": expenditure, "full_pass_estimate_usd": estimate,
                "retry_api_usd": sum(c["retry_api_usd"] for c in costs),
                "uncosted_attempts": sum(c["uncosted_attempts"] for c in costs)}
            lines.append(f"| {name} | {len(selected)} | {finished}/{len(passes)} | {completed}/{expected} | {flags} | {len(flagged_ids)} | {rate} | {money} |")
        lines += ["", "### Correlation matrix", "",
                  "| Model | " + " | ".join(models) + " |", "|---|" + "---:|" * len(models)]
        cache = {}
        for first, passes in models.items():
            cells = []
            for second, others in models.items():
                key = tuple(sorted((first, second)))
                if key not in cache:
                    if first == second and len(passes) < 2:
                        cache[key] = {"n": 0, "r": None, "ci95": None, "reason": "no repeat pass"}
                    else:
                        a = passes[0]["results"]
                        b = passes[1]["results"] if first == second else others[0]["results"]
                        cache[key] = correlation(a, b, scoped, positive, f"{audit}:{lib}:{key}", resamples)
                estimate = cache[key]
                group["correlations"][f"{first}/{second}"] = estimate
                if estimate["r"] is None:
                    cells.append("—" + (f"; n={estimate['n']}" if estimate["n"] else ""))
                else:
                    ci = estimate["ci95"]
                    interval = f" [{ci[0]:.2f}, {ci[1]:.2f}]" if ci else " [—]"
                    cells.append(f"{estimate['r']:.2f}{interval}; n={estimate['n']}")
            lines.append(f"| {first} | " + " | ".join(cells) + " |")
        if is_file:
            lines += ["", "Coverage annotations: " + "; ".join(f"{name}: {row['partial_reviews']} partial, {row['not_applicable_reviews']} not applicable" for name, row in group["models"].items()) + "."]
        data["groups"][lib or "all"] = group
        lines.append("")
    position = lines.index("## All libraries")
    lines[position:position] = ["## Library comparison", "", *library_table(data, libraries, names), ""]
    destination = FILES / "reports" / f"{audit}-comparison" if is_file else base / "audit-comparison"
    destination.with_suffix(".md").write_text("\n".join(lines))
    destination.with_suffix(".json").write_text(json.dumps(data, indent=2) + "\n")
    return destination.with_suffix(".md")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--resamples", type=int, default=2000)
    args = parser.parse_args()
    if args.resamples < 100:
        parser.error("Use at least 100 bootstrap resamples")
    sections = []
    for audit, is_file in [("unnecessary-hypotheses", False), ("duplicates-mathlib-inclusive", False), *[(r, True) for r in RUBRICS]]:
        run = FILES if is_file else MAIN
        samples = {s["id"]: s for s in map(json.loads, (run / "samples.jsonl").read_text().splitlines())}
        path = make_report(audit, run / audit, samples, is_file, args.resamples)
        text = path.read_text()
        library_section = text.split("## Library comparison\n", 1)[1].split("\n## ", 1)[0].strip()
        section = text.split("## All libraries\n", 1)[1].split("\n## ", 1)[0].strip()
        section = section.replace("### Correlation matrix", "#### Correlation matrix")
        note = ("Opus uses the earlier prompt on four libraries, without Mathlib targets.\n\n"
                if audit == "duplicates-mathlib-inclusive" else "")
        sections.append(f"## {audit}\n\n[Library breakdowns]({path.relative_to(ROOT).as_posix()})\n\n" + note +
                        "### Library comparison\n\n" + library_section + "\n\n### Model comparison\n\n" + section)
        print(path.relative_to(ROOT), flush=True)
    (ROOT / "AUDIT_RESULTS.md").write_text("# Audit results\n\n" +
        f"Generated {datetime.datetime.now(datetime.timezone.utc).isoformat(timespec='seconds')} · " +
        "[Methods and notation](AUDIT_METHODS.md) · [Cost summary](runs/main/api-equivalent-costs.md).\n\n" +
        "All eight audits, comparing libraries first and models second.\n\n" + "\n\n".join(sections) + "\n")


if __name__ == "__main__":
    main()
