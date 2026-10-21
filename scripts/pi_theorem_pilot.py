"""Small, blind pi reproductions of the two theorem audits with pairwise reports."""

import argparse
import hashlib
import itertools
import json
from pathlib import Path
import tomllib

import duplicates_judge
import indicator
import judge
import pi_judge
from agreement import hyp_keys, kappa

ROOT = Path(__file__).resolve().parent.parent
INDICATORS = ["unnecessary-hypotheses", "duplicates-mathlib-inclusive"]
BASELINES = {"Sol": "gpt-6.1-sol-high", "Luna": "gpt-6-luna-high",
             "Sonnet": "claude-sonnet-5-5-high"}


def write_json(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(".tmp")
    tmp.write_text(json.dumps(value, indent=2) + "\n")
    tmp.replace(path)


def load_ids(base):
    return [p.stem for p in (base / "results").glob("*.json")
            if p.stem.rsplit("-", 1)[-1].isdigit()]


def report(run, audit, label, samples):
    base = run / audit
    models = {**BASELINES, "GLM": label}
    results = {name: {s["id"]: json.loads(p.read_text()) for s in samples
                     if (p := base / model / "results" / f"{s['id']}.json").exists()}
               for name, model in models.items()}
    positive = indicator.config(ROOT / "indicators" / audit)["positive"]
    libraries = {lib["id"]: lib["name"] for lib in
                 tomllib.loads((ROOT / "libraries.toml").read_text())["library"]}
    lines = [f"# {audit}: pi GLM pilot", "",
             "Same first sampled theorems; one blind high-effort pass per model. "
             "Cells show positive judgments / completed judgments. No missing judgment is counted as negative.", "",
             "| Library | " + " | ".join(models) + " |",
             "|---|" + "---:|" * len(models)]
    for lib, name in libraries.items():
        ids = [s["id"] for s in samples if s["lib"] == lib]
        cells = []
        for rows in results.values():
            completed = [rows[i] for i in ids if i in rows]
            cells.append(f"{sum(r['verdict'] in positive for r in completed)}/{len(completed)}")
        lines.append(f"| {name} | " + " | ".join(cells) + " |")
    lines += ["", "## Pairwise agreement", "",
              "Pairs use only IDs completed by both models in the fixed pilot selection. "
              "Hypothesis details compare binder names; duplicate details compare canonical declaration names.", "",
              "| First | Second | Library | N | Agree | Both positive | Same detail among both | κ |",
              "|---|---|---|---:|---:|---:|---:|---:|"]
    for first, second in itertools.combinations(models, 2):
        for lib, name in [*libraries.items(), (None, "All")]:
            ids = [s["id"] for s in samples if (lib is None or s["lib"] == lib)
                   and s["id"] in results[first] and s["id"] in results[second]]
            pairs = [(results[first][i]["verdict"] in positive,
                      results[second][i]["verdict"] in positive) for i in ids]
            both = [i for i, (a, b) in zip(ids, pairs) if a and b]
            if audit == "unnecessary-hypotheses":
                same = sum(bool(hyp_keys(results[first][i]) & hyp_keys(results[second][i])) for i in both)
            else:
                same = sum(duplicates_judge.canonical_name(results[first][i]["mathlib_declaration"]) ==
                           duplicates_judge.canonical_name(results[second][i]["mathlib_declaration"]) for i in both)
            agreement = f"{sum(a == b for a, b in pairs) / len(pairs):.1%}" if pairs else "—"
            # κ is undefined when both judges give the same constant classification.
            constant = pairs and (all(a and b for a, b in pairs) or all(not a and not b for a, b in pairs))
            coefficient = f"{kappa(pairs):.3f}" if pairs and not constant else "—"
            lines.append(f"| {first} | {second} | {name} | {len(pairs)} | {agreement} | "
                         f"{len(both)} | {same}/{len(both)} | {coefficient} |")
    lines += ["", "Flags and replacement arguments are model judgments. This small pilot has substantial sampling uncertainty."]
    (base / label / "pairwise-agreement.md").write_text("\n".join(lines) + "\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--limit", type=int, default=10)
    parser.add_argument("--model", default="z-ai/glm-5.3")
    parser.add_argument("--pi-provider", default="openrouter")
    parser.add_argument("--label", default="glm-5.3-openrouter-pi-high-pilot")
    parser.add_argument("--report-only", action="store_true")
    parser.add_argument("--update-runner-only", action="store_true",
                        help="record a runner-only provenance update without making model calls")
    args = parser.parse_args()
    args.effort, args.timeout, args.retries = "high", 1800, 2
    if args.limit < 1 or Path(args.label).name != args.label:
        parser.error("Use a positive limit and simple label")
    run = ROOT / "runs/main"
    selection = argparse.Namespace(libs=None, ids=None, limit=args.limit)
    samples = judge.select_samples([json.loads(line) for line in
                                   (run / "samples.jsonl").read_text().splitlines()], selection)
    if args.report_only:
        for audit in INDICATORS:
            (run / audit / args.label).mkdir(parents=True, exist_ok=True)
            report(run, audit, args.label, samples)
        return
    version = pi_judge.preflight(args)
    hashes = {name: hashlib.sha256((ROOT / "scripts" / name).read_bytes()).hexdigest() for name in
              ["pi_theorem_pilot.py", "pi_judge.py", "judge.py", "duplicates_judge.py", "source_tools.py", "agreement.py"]}
    for name in ["session.mjs", "package-lock.json"]:
        hashes["tools/pi/" + name] = hashlib.sha256((ROOT / "tools/pi" / name).read_bytes()).hexdigest()
    for audit in INDICATORS:
        base = run / audit / args.label
        (base / "results").mkdir(parents=True, exist_ok=True)
        ind = ROOT / "indicators" / audit
        protocol = {"backend": "pi", "provider": args.pi_provider, "model": args.model,
                    "effort": "high", "indicator": audit, "code_hashes": hashes,
                    "corpus_sha256": hashlib.sha256((ROOT / "libraries.lock.json").read_bytes()).hexdigest(),
                    "artifacts": {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in ind.iterdir() if p.is_file()},
                    "sample_ids": [s["id"] for s in samples]}
        manifest = base / "judge.json"
        metadata = json.loads(manifest.read_text()) if manifest.exists() else {}
        if metadata and metadata["protocol"] != protocol:
            old = metadata["protocol"]
            if not args.update_runner_only or {k:v for k,v in old.items() if k != "code_hashes"} != {k:v for k,v in protocol.items() if k != "code_hashes"}:
                raise SystemExit("Saved pi pilot protocol differs; choose a new label")
            metadata.setdefault("runner_history", []).append({
                "code_hashes": old["code_hashes"], "accepted_ids": sorted(load_ids(base)),
                "reason": "Explicit runner-only update; prompts, sources, schema, selection and effort unchanged"})
        write_json(manifest, {**metadata, "protocol": protocol, "cli_version": version})
        report(run, audit, args.label, samples)
    if args.update_runner_only:
        return
    libraries = list(dict.fromkeys(s["lib"] for s in samples))
    by_lib = {lib: [s for s in samples if s["lib"] == lib] for lib in libraries}
    for index in range(args.limit):
        for lib in libraries:
            sample = by_lib[lib][index]
            for audit in INDICATORS:
                out = run / audit / args.label / "results"
                path = out / f"{sample['id']}.json"
                if path.exists():
                    continue
                ind = ROOT / "indicators" / audit
                cwd, dirs, message = judge.build_message(sample, run, ind)
                # The duplicate-specific validator excludes self-matches in Mathlib.
                judge.validate_verdict = duplicates_judge.validate if audit == INDICATORS[1] else duplicates_judge.original_validate
                duplicates_judge.context.sample = sample
                try:
                    result = pi_judge.judge(sample, ind, out, args, cwd, dirs, message)
                finally:
                    del duplicates_judge.context.sample
                write_json(path, result)
                print(json.dumps({"audit": audit, "id": sample["id"], "verdict": result["verdict"]}), flush=True)
                report(run, audit, args.label, samples)


if __name__ == "__main__":
    main()
