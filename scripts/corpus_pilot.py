"""Isolated OpenAI Math samples: select 2000 theorem/file targets, judge the first 100.

python3 scripts/corpus_pilot.py prepare
python3 scripts/corpus_pilot.py dependencies
python3 scripts/corpus_pilot.py judge --model Sol

Each model defaults to one worker; --jobs increases concurrent independent sessions. Prompts and common validators are reused unchanged;
source/dependency roots and protocol hashes belong to this corpus, not runs/main.
"""
import argparse
from concurrent.futures import ProcessPoolExecutor
import datetime
import fcntl
import hashlib
import json
import multiprocessing
import os
from pathlib import Path
import random
import subprocess
import sys
import time

import duplicates_judge
import file_audits
import judge
import sample

ROOT = Path(__file__).resolve().parent.parent
BASE = ROOT / "runs/openai-math-2026-10-21"
SOURCE = ROOT / "repos/openai-math"
COMMIT = "1581d4cbdd69a0faf34b2089614fe2a814316a6a"
AUDITS = [("unnecessary-hypotheses", "theorem"), ("duplicates-mathlib-inclusive", "theorem"),
          *[(r, "file") for r in file_audits.RUBRICS]]
MODELS = {"Opus": ("claude", "claude-opus-5-5"), "Sol": ("codex", "gpt-6.1-sol"),
          "Sonnet": ("claude", "claude-sonnet-5-5"), "Luna": ("codex", "gpt-6-luna")}
ORIGINAL_VALIDATE = duplicates_judge.original_validate
CONFIG = '''[defaults]
exclude = ["*/Certificates/*"]
skip_deprecated = true
skip_private = true
[[library]]
id = "openai-math"
name = "OpenAI Math"
[[library.source]]
dir = "openai-math"
url = "https://github.com/openai/math"
include = ["lean/OAI/"]
exclude = []
'''


def digest(data):
    return hashlib.sha256(data).hexdigest()


def save(path, value):
    file_audits.write_json(path, value)


def utc():
    return datetime.datetime.now(datetime.timezone.utc).isoformat(timespec="seconds")


def setup():
    BASE.mkdir(parents=True, exist_ok=True)
    actual = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=SOURCE, text=True).strip()
    if actual != COMMIT:
        raise ValueError("OpenAI Math checkout differs from the selected commit")
    config = BASE / "libraries.toml"
    if config.exists() and config.read_text() != CONFIG:
        raise ValueError("Corpus configuration changed")
    if not config.exists():
        config.write_text(CONFIG)
    lock = {"openai-math": {"url": "https://github.com/openai/math", "commit": COMMIT}}
    path = BASE / "libraries.lock.json"
    if path.exists() and json.loads(path.read_text()) != lock:
        raise ValueError("Corpus lock changed")
    if not path.exists():
        save(path, lock)
    repos = BASE / "repos"
    if not repos.exists():
        repos.symlink_to(ROOT / "repos", target_is_directory=True)
    sample.ROOT = BASE
    file_audits.ROOT = BASE
    return sample.load_config()


def prepare(selected):
    cfg, lock = setup()
    run = BASE / "theorems"
    run.mkdir(exist_ok=True)
    destination = run / "samples.jsonl"
    if not destination.exists():
        population, info = sample.population(cfg, lock, cfg["library"][0], 8)
        picked = random.Random("0:openai-math").sample(range(len(population)), selected)
        src = cfg["library"][0]["source"][0]
        rows = []
        for index, number in enumerate(picked):
            row = population[number]
            sid = f"openai-math-{index:04d}"
            snippet, _ = sample.extract(lock, src, row)
            target = f"samples/openai-math/{sid}.lean"
            (run / target).parent.mkdir(parents=True, exist_ok=True)
            (run / target).write_text(snippet)
            rows.append({"id": sid, **row, "commit": COMMIT, "file": target,
                         "url": f"https://github.com/openai/math/blob/{COMMIT}/{row['path']}#L{row['line']}",
                         "snippet_lines": snippet.count("\n"), "snippet_chars": len(snippet)})
        destination.write_text("".join(json.dumps(row) + "\n" for row in rows))
        save(run / "run.json", {"seed": 0, "n": selected, "population": {"openai-math": info},
                                 "commit": COMMIT, "created": utc()})
    elif len(destination.read_text().splitlines()) != selected:
        raise ValueError("Selection size differs from the saved sample")
    rows, _ = file_audits.prepare(BASE / "files", selected, 0, ["openai-math"])
    save(BASE / "experiment.json", {"corpus": "OpenAI Math", "commit": COMMIT,
         "source_scope": "lean/OAI/; excluding ComparatorChallenges statement specifications",
         "selected_per_unit": selected, "initial_judged_per_audit_model": 100,
         "audits": [a for a, _ in AUDITS], "models": MODELS,
         "selection": "theorems: original seeded sampler; files: original SHA256 ordering",
         "created": utc()})
    print(f"Selected {selected} theorems and {len(rows)} complete files", flush=True)


def dependency_records():
    return json.loads((SOURCE / "lean/lake-manifest.json").read_text())["packages"]


def dependency_dir(package):
    name = package["name"].strip("«»")
    return ROOT / "repos/deps" / f"{name}-{package['rev'][:12]}"


def dependencies():
    setup()
    for package in dependency_records():
        target = dependency_dir(package)
        if target.exists():
            commit = subprocess.run(["git", "rev-parse", "HEAD"], cwd=target,
                                    capture_output=True, text=True)
            if commit.returncode == 0 and commit.stdout.strip() == package["rev"]:
                continue
            raise ValueError(f"Incomplete or different dependency checkout: {target}")
        temporary = target.with_name(target.name + ".fetching")
        temporary.mkdir(parents=True, exist_ok=True)
        if not (temporary / ".git").exists():
            subprocess.run(["git", "init", "-q"], cwd=temporary, check=True)
            subprocess.run(["git", "remote", "add", "origin", package["url"]], cwd=temporary, check=True)
        print(f"Fetching {package['name']} {package['rev'][:12]}", flush=True)
        subprocess.run(["git", "fetch", "-q", "--depth", "1", "origin", package["rev"]], cwd=temporary, check=True)
        subprocess.run(["git", "checkout", "-q", "--detach", "FETCH_HEAD"], cwd=temporary, check=True)
        temporary.rename(target)
    save(BASE / "dependencies.json", dependency_records())


def source_dirs(row, mathlib="pinned"):
    # Preserve each audit's choice of current-master versus pinned Mathlib.
    dirs = {}
    for package in dependency_records():
        name = package["name"].strip("«»")
        if name == "mathlib" and mathlib == "master":
            dirs["Mathlib (current master)"] = ROOT / "repos/mathlib"
            continue
        path = dependency_dir(package)
        if not path.is_dir():
            raise ValueError(f"Missing pinned dependency: {path}")
        dirs[f"{name} (pinned {package['rev'][:12]})"] = path
    toolchain = (SOURCE / "lean/lean-toolchain").read_text().strip()
    core = Path.home() / ".elan/toolchains" / toolchain.replace("/", "--").replace(":", "---") / "src/lean"
    if not core.is_dir():
        raise ValueError(f"Missing Lean core sources: {core}")
    dirs[f"Lean core ({toolchain})"] = core
    return SOURCE, dirs


def rows_for(unit):
    return [json.loads(line) for line in (BASE / ("files" if unit == "file" else "theorems") / "samples.jsonl").read_text().splitlines()]


def task_belongs(index, worker, jobs):
    return index % jobs == worker


def model_status(name, limit, **extra):
    """Serialize status writes and count saved judgments across all workers."""
    with (BASE / f"{name}-status-lock.log").open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        label = MODELS[name][1] + "-high"
        done = sum(p.stem.rsplit("-", 1)[-1].isdigit()
                   for p in BASE.glob(f"*/*/{label}/results/*.json"))
        expected = limit * len(AUDITS)
        save(BASE / f"{name}-status.json", {"utc": utc(), "pid": os.getpid(),
             "new_judgments": done, "planned": expected,
             "stage": "complete" if done == expected else "running", **extra})


def run_model(name, limit, worker=0, jobs=1):
    setup()
    backend, model = MODELS[name]
    label = model + "-high"
    with (BASE / f"{name}-worker-{worker}-controller.log").open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        args = argparse.Namespace(backend=backend, model=model, effort="high", timeout=1800, retries=2,
                  max_budget=5, claude=os.environ.get("CLAUDE_BIN", "claude"),
                  codex=str(ROOT / "scripts/codex_rate_guard.py"))
        executable = args.claude if backend == "claude" else args.codex
        version = subprocess.check_output([executable, "--version"], text=True).strip()
        hashes = {p.name: digest(p.read_bytes()) for p in (ROOT / "scripts").glob("*.py")
                  if not p.name.startswith("test_") and p.name not in ["audit_dashboard.py", "api_costs.py", "order_model_tables.py", "watch_audit_reports.py"]}
        judge.judge_dirs = source_dirs
        tasks = []
        for audit, unit in AUDITS:
            run = BASE / ("files" if unit == "file" else "theorems")
            ind = run / "protocols" / audit if unit == "file" else ROOT / "indicators" / audit
            selected = rows_for(unit)[:limit]
            directory = run / audit / label
            (directory / "results").mkdir(parents=True, exist_ok=True)
            protocol = {"backend": backend, "model": model, "effort": "high", "audit": audit,
                        "sample_ids": [r["id"] for r in selected], "selected_population_targets": len(rows_for(unit)),
                        "sample_sha256": digest((run / "samples.jsonl").read_bytes()), "commit": COMMIT,
                        "code_hashes": hashes, "dependencies": dependency_records(),
                        "artifacts": {p.name: digest(p.read_bytes()) for p in ind.iterdir() if p.is_file()}}
            manifest = directory / "judge.json"
            with (directory / "manifest-lock.log").open("a") as manifest_lock:
                fcntl.flock(manifest_lock, fcntl.LOCK_EX)
                if manifest.exists():
                    if json.loads(manifest.read_text())["protocol"] != protocol:
                        raise ValueError("Saved judge protocol differs; use a new label")
                else:
                    save(manifest, {"protocol": protocol, "cli_version": version})
            tasks.extend((i, audit, unit, row, run, ind, directory) for i, row in enumerate(selected))
        model_status(name, limit, jobs=jobs)
        # Interleave audits so each gets early data before a larger pass completes.
        for index, audit, unit, row, run, ind, directory in sorted(tasks, key=lambda task: task[0]):
            if not task_belongs(index, worker, jobs):
                continue
            destination = directory / "results" / f"{row['id']}.json"
            if destination.exists():
                continue
            source_dirs(row, "pinned")
            try:
                if unit == "file":
                    judge.validate_verdict = file_audits.validate
                    judge.build_message = file_audits.build_message
                    result = file_audits.review(row, audit, run, label, args)
                else:
                    judge.validate_verdict = duplicates_judge.validate if audit.startswith("duplicates") else ORIGINAL_VALIDATE
                    judge.build_message = file_audits.original_build_message
                    duplicates_judge.context.sample = row
                    try:
                        result = judge.judge_one(row, run, ind, directory / "results", args)
                        save(destination, result)
                    finally:
                        del duplicates_judge.context.sample
            except RuntimeError as error:
                if not str(error).startswith("Invalid verdict:"):
                    raise  # Infrastructure or source-access failures still stop the worker.
                failure = {"utc": utc(), "audit": audit, "id": row["id"], "error": str(error)}
                save(directory / "results" / f"{row['id']}.failure.json", failure)
                print(json.dumps({"rejected": failure}), flush=True)
                model_status(name, limit, jobs=jobs, latest_rejection=failure)
                continue  # Leave this target unanswered; finish other selected targets.
            (directory / "results" / f"{row['id']}.failure.json").unlink(missing_ok=True)
            model_status(name, limit, jobs=jobs, latest_audit=audit, latest_id=row["id"])
            print(json.dumps({"audit": audit, "id": row["id"], "verdict": result["verdict"]}), flush=True)
            time.sleep(5)
        model_status(name, limit, jobs=jobs)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=["prepare", "dependencies", "judge"])
    parser.add_argument("--selected", type=int, default=2000)
    parser.add_argument("--limit", type=int, default=100)
    parser.add_argument("--model", choices=MODELS)
    parser.add_argument("--jobs", type=int, default=1)
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("jobs must be positive")
    if not 1 <= args.limit <= args.selected:
        parser.error("Require 1 <= limit <= selected")
    if args.action == "prepare":
        prepare(args.selected)
    elif args.action == "dependencies":
        dependencies()
    elif not args.model:
        parser.error("judge requires --model")
    elif args.jobs == 1:
        run_model(args.model, args.limit)
    else:
        with ProcessPoolExecutor(args.jobs) as pool:
            futures = [pool.submit(run_model, args.model, args.limit, worker, args.jobs)
                       for worker in range(args.jobs)]
            for future in futures:
                future.result()


if __name__ == "__main__":
    multiprocessing.set_start_method("fork")
    main()
