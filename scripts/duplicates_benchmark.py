"""Queue one duplicate pass per model, including Mathlib, with a slow initial phase.

    python3 -u scripts/duplicates_benchmark.py --slow-spacing 180 --limit 1000

Starts at most one session per model every three minutes until the existing
hypothesis benchmark's success marker appears. Then uses eight queued workers
per Codex model behind the shared guard (nine active total), and two for Sonnet.
The input corpus and original duplicates-mathlib experiment are preserved.
"""

import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time
import tomllib

import codex_rate_guard as guard
import duplicate_pace as pace
import judge

ROOT = Path(__file__).resolve().parent.parent
INDICATOR = "duplicates-mathlib-inclusive"
BASE = ROOT / "runs/main" / INDICATOR
MODELS = [("codex", "gpt-6.1-sol", 8), ("codex", "gpt-6-luna", 8),
          ("claude", "claude-sonnet-5-5", 2)]


def load_results(label):
    rows = {}
    for path in (BASE / label / "results").glob("*.json"):
        if path.stem.rsplit("-", 1)[-1].isdigit():
            rows[path.stem] = json.loads(path.read_text())
    return rows


def atomic_json(path, value):
    temporary = path.with_suffix(".tmp")
    temporary.write_text(json.dumps(value, indent=2) + "\n")
    temporary.replace(path)


def comparison(samples):
    """Compare matching IDs with saved original Opus duplicate results."""
    libraries = tomllib.loads((ROOT / "libraries.toml").read_text())["library"]
    labels = [f"{model}-high" for _, model, _ in MODELS]
    results = {label: load_results(label) for label in labels}
    baseline = ROOT / "runs/main/duplicates-mathlib/claude-opus-5-5-high/results"
    positive = {"duplicate", "special_case"}
    lines = ["# Duplicates in Mathlib: model comparison", "",
             "One pass per model; flags are judge claims, not compiled proofs.", "",
             "Mathlib excludes the target declaration and circular justifications. "
             "Opus used the original protocol on the other four libraries.", "",
             "| Library | Sample size | Opus | Sol | Luna | Sonnet |",
             "|---|---:|---:|---:|---:|---:|"]
    for lib in libraries:
        ids = [s["id"] for s in samples if s["lib"] == lib["id"]]
        if any(not set(ids) <= rows.keys() for rows in results.values()):
            raise RuntimeError("Incomplete duplicate comparison")
        paths = [baseline / f"{i}.json" for i in ids]
        opus = str(sum(json.loads(p.read_text())["verdict"] in positive for p in paths)) \
            if all(p.exists() for p in paths) else "—"
        counts = [sum(results[label][i]["verdict"] in positive for i in ids) for label in labels]
        lines.append(f"| {lib['name']} | {len(ids)} | {opus} | " + " | ".join(map(str, counts)) + " |")
    (BASE / "model-comparison.md").write_text("\n".join(lines) + "\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--slow-spacing", type=float, default=180)
    parser.add_argument("--limit", type=int, default=1000)
    args = parser.parse_args()
    if args.slow_spacing < 60 or not 1 <= args.limit <= 1000:
        parser.error("Slow spacing must be at least 60 seconds; limit must be 1..1000")
    BASE.mkdir(parents=True, exist_ok=True)
    # Refuse a duplicate controller, including accidental relaunches in another turn.
    lock = (BASE / "benchmark-lock.log").open("a")
    import fcntl
    fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    selection = argparse.Namespace(libs=None, ids=None, limit=args.limit)
    samples = judge.select_samples([json.loads(line) for line in
                                   (ROOT / "runs/main/samples.jsonl").read_text().splitlines()], selection)
    # Check all source roots and messages before starting billable sessions.
    for sample in samples:
        judge.build_message(sample, ROOT / "runs/main", ROOT / "indicators" / INDICATOR)
    labels = [f"{model}-high" for _, model, _ in MODELS]
    policy = {"indicator": INDICATOR, "limit_per_library": args.limit, "passes": 1,
              "models": labels, "gate": str(pace.GATE), "slow_start_spacing_seconds": args.slow_spacing,
              "slow_active_sessions_per_model": 1, "shared_codex_ceiling": 9,
              "full_sonnet_sessions": 2, "pid": os.getpid(),
              "started_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(timespec="seconds"),
              "hashes": {name: hashlib.sha256((ROOT / "scripts" / name).read_bytes()).hexdigest()
                         for name in ["duplicates_benchmark.py", "duplicates_judge.py",
                                      "duplicate_pace.py", "codex_rate_guard.py"]}}
    atomic_json(BASE / "execution-policy.json", policy)
    workers = []
    for backend, model, jobs in MODELS:
        label = f"{model}-high"
        env = dict(os.environ, DUPLICATE_SLOW_SPACING=str(args.slow_spacing),
                   DUPLICATE_REAL_BIN=str(ROOT / "scripts/codex_rate_guard.py") if backend == "codex"
                   else os.environ.get("CLAUDE_BIN", "claude"))
        env["CODEX_BIN" if backend == "codex" else "CLAUDE_BIN"] = str(ROOT / "scripts/duplicate_pace.py")
        cmd = [sys.executable, "-u", "scripts/duplicates_judge.py", "--run", "main", "--indicator", INDICATOR,
               "--backend", backend, "--model", model, "--effort", "high", "--label", label,
               "--limit", str(args.limit), "--jobs", str(jobs), "--timeout", "3600"]
        output = (BASE / f"{label}.log").open("a")
        proc = subprocess.Popen(cmd, cwd=ROOT, env=env, stdout=output, stderr=subprocess.STDOUT)
        workers.append({"label": label, "process": proc, "log": output, "command": cmd,
                        "env": env, "launches": 1, "retry_after": 0})
    tuner = None
    while True:
        now = time.time()
        full = pace.GATE.exists()
        if full and tuner is None:
            output = (BASE / "maintenance-driver.log").open("a")
            tuner = subprocess.Popen([sys.executable, "-u", "scripts/tune_codex.py", "--minutes", "1440",
                                      "--max-sessions", "9", "--spacing", "3", "--interval", "60",
                                      "--completion-marker", str(BASE / "benchmark-complete.json")],
                                     cwd=ROOT, stdout=output, stderr=subprocess.STDOUT)
            output.close()
        status = {"utc": datetime.datetime.now(datetime.timezone.utc).isoformat(timespec="seconds"),
                  "phase": "full" if full else "slow", "completed": {}, "workers": {},
                  "guard": guard.snapshot(), "tuner_pid": tuner.pid if tuner else None}
        for worker in workers:
            proc = worker["process"]
            code = proc.poll()
            if code and worker["launches"] < 3:
                if not worker["retry_after"]:
                    worker["retry_after"] = now + 300
                elif now >= worker["retry_after"]:
                    worker["process"] = subprocess.Popen(worker["command"], cwd=ROOT, env=worker["env"],
                                                         stdout=worker["log"], stderr=subprocess.STDOUT)
                    worker["launches"] += 1
                    worker["retry_after"] = 0
                    code = None
            rows = load_results(worker["label"])
            status["completed"][worker["label"]] = {
                lib: {"judged": sum(r["lib"] == lib for r in rows.values()),
                      "flagged": sum(r["lib"] == lib and r["verdict"] != "none_found" for r in rows.values())}
                for lib in dict.fromkeys(s["lib"] for s in samples)}
            status["workers"][worker["label"]] = {"pid": worker["process"].pid, "exit_code": code,
                                                  "launches": worker["launches"]}
        if tuner and tuner.poll() is not None and not (BASE / "benchmark-complete.json").exists():
            status["maintenance_error"] = f"Controller exited with {tuner.returncode}"
        atomic_json(BASE / "status.json", status)
        print(json.dumps(status), flush=True)
        if all(w["process"].poll() is not None and not w["retry_after"] for w in workers):
            break
        time.sleep(60)
    if any(w["process"].returncode for w in workers):
        raise SystemExit("Duplicate run failed after retries; see worker logs and status.json")
    for label in labels:
        subprocess.run([sys.executable, "scripts/report.py", "--run", "main", "--indicator", INDICATOR,
                        "--label", label], cwd=ROOT, check=True, capture_output=True)
    comparison(samples)
    atomic_json(BASE / "benchmark-complete.json", {"labels": labels, "limit": args.limit})
    print("Duplicate reproduction complete", flush=True)


if __name__ == "__main__":
    main()
