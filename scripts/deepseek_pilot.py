"""Matched eight-audit DeepSeek pilot: 1440 judgments, $20 API inference cap."""
import argparse
import datetime
import hashlib
import json
from pathlib import Path
import time
import subprocess
import fcntl

import corpus_pilot
import duplicates_judge
import file_audits
import judge
import openrouter_judge as backend
from source_tools import Sources

ROOT = Path(__file__).resolve().parent.parent
BASE = ROOT / "runs/deepseek-pilot-2026-10-21"
LABEL = "deepseek-v4.1-flash-1017-openrouter-high"
AUDITS = corpus_pilot.AUDITS
ORIGINAL_DIRS = judge.judge_dirs


def sources(row, mode="pinned"):
    return corpus_pilot.source_dirs(row, mode) if row["lib"] == "openai-math" else ORIGINAL_DIRS(row, mode)


def read_rows(run):
    return [json.loads(line) for line in (run / "samples.jsonl").read_text().splitlines()]


def selection():
    main, files = ROOT / "runs/main", ROOT / "runs/file-quality-pilot-2026-10-21"
    extra = corpus_pilot.BASE
    theorem_rows = [(row, main) for row in read_rows(main) if int(row["id"].rsplit("-", 1)[1]) < 100]
    theorem_rows += [(row, extra / "theorems") for row in read_rows(extra / "theorems")[:100]]
    file_rows = [(row, files) for row in read_rows(files)]
    file_rows += [(row, extra / "files") for row in read_rows(extra / "files")[:10]]
    tasks = []
    for order, (audit, unit) in enumerate(AUDITS):
        pairs = file_rows if unit == "file" else theorem_rows
        output = (files if unit == "file" else main) / audit / LABEL
        for row, run in pairs:
            ind = run / "protocols" / audit if unit == "file" else ROOT / "indicators" / audit
            tasks.append({"audit": audit, "unit": unit, "row": row, "run": str(run.relative_to(ROOT)),
                          "indicator": str(ind.relative_to(ROOT)), "output": str(output.relative_to(ROOT)),
                          "order": [int(row["id"].rsplit("-", 1)[1]), order, row["lib"]]})
    return sorted(tasks, key=lambda task: task["order"])


def prepare(accept_harness_update=False):
    BASE.mkdir(parents=True, exist_ok=True)
    tasks = selection()
    checked = set()
    for task in tasks:
        row = task["row"]
        repo = ROOT / "repos" / row["dir"]
        if row["dir"] not in checked:
            actual = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=repo, text=True).strip()
            if actual != row["commit"]:
                raise ValueError(f"Source commit changed: {row['dir']}")
            checked.add(row["dir"])
        if task["unit"] == "file" and hashlib.sha256((repo / row["path"]).read_bytes()).hexdigest() != row["source_sha256"]:
            raise ValueError("Target source changed")
    path = BASE / "selection.json"
    if path.exists() and json.loads(path.read_text()) != tasks:
        raise ValueError("Saved selection differs")
    backend.write_json(path, tasks)
    hashes = {name: hashlib.sha256((ROOT / "scripts" / name).read_bytes()).hexdigest() for name in
              ["deepseek_pilot.py", "openrouter_judge.py", "source_tools.py", "judge.py", "file_audits.py",
               "duplicates_judge.py", "corpus_pilot.py"]}
    for audit, unit in AUDITS:
        selected = [task for task in tasks if task["audit"] == audit]
        directory = ROOT / selected[0]["output"]
        (directory / "results").mkdir(parents=True, exist_ok=True)
        ind = ROOT / selected[0]["indicator"]
        protocol = {"model": backend.MODEL, "backend": "openrouter", "provider": backend.PROVIDER, "provider_slug": backend.PROVIDER_SLUG,
                    "allow_provider_fallbacks": False, "effort": "high", "unit": unit, "audit": audit,
                    "sample_ids": [task["row"]["id"] for task in selected], "code_hashes": hashes,
                    "selection_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
                    "artifacts": {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in ind.iterdir() if p.is_file()},
                    "source_runs": sorted({task["run"] for task in selected}),
                    "max_output_tokens_per_request": backend.MAX_OUTPUT,
                    "max_tool_turns_per_judgment": backend.MAX_TOOL_TURNS,
                    "max_final_attempts": backend.MAX_FINAL_ATTEMPTS,
                    "resumable_sessions": True, "judgment_admission_limit_usd": .50}
        manifest = directory / "judge.json"
        if manifest.exists() and json.loads(manifest.read_text())["protocol"] != protocol:
            if not accept_harness_update:
                raise ValueError("Saved pilot protocol changed; inspect and explicitly accept the harness update")
            value = json.loads(manifest.read_text())
            value.setdefault("protocol_history", []).append({"protocol": value["protocol"],
                "accepted_ids": sorted(p.stem for p in (directory / "results").glob("*.json") if p.stem.rsplit("-", 1)[-1].isdigit()),
                "utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
                "reason": "Repair DeepSeek harness: switch overloaded DeepInfra FP8 to InferenceNet FP8, resume paid tool sessions, supply working directory, reserve final JSON phase after 32 source turns, and repair invalid JSON/evidence. Audit prompts, source snapshots and selected targets unchanged."})
            value["protocol"] = protocol
            backend.write_json(manifest, value)
        if not manifest.exists():
            backend.write_json(manifest, {"protocol": protocol})
    return tasks


def update_runner():
    hashes = {name: hashlib.sha256((ROOT / "scripts" / name).read_bytes()).hexdigest() for name in
              ["deepseek_pilot.py", "openrouter_judge.py", "source_tools.py", "judge.py", "file_audits.py",
               "duplicates_judge.py", "corpus_pilot.py"]}
    for audit, unit in AUDITS:
        base = ROOT / ("runs/file-quality-pilot-2026-10-21" if unit == "file" else "runs/main")
        path = base / audit / LABEL / "judge.json"
        if not path.exists(): continue
        manifest = json.loads(path.read_text())
        old = manifest["protocol"]["code_hashes"]
        if old == hashes: continue
        manifest.setdefault("runner_history", []).append({"code_hashes": old,
            "accepted_ids": sorted(p.stem for p in (path.parent / "results").glob("*.json") if p.stem.rsplit("-",1)[-1].isdigit()),
            "reason": "Explicit runner-only plumbing update; sources, prompts, schema, model settings and targets unchanged"})
        manifest["protocol"]["code_hashes"] = hashes
        backend.write_json(path, manifest)


def off_peak(now):
    return now.weekday() >= 5 or now.hour not in {1, 2, 3, 6, 7, 8, 9}


def status(stage, tasks, budget, **extra):
    completed = sum((ROOT / t["output"] / "results" / f"{t['row']['id']}.json").exists() for t in tasks)
    state = budget.read()
    backend.write_json(BASE / "status.json", {"utc": datetime.datetime.now(datetime.timezone.utc).isoformat(timespec="seconds"),
        "stage": stage, "completed": completed, "planned": len(tasks), "billed_usd": state["billed_usd"],
        "limit_usd": state["limit_usd"], **extra})
    return completed


def evaluate(task, key, budget):
    row, unit = task["row"], task["unit"]
    run, ind = ROOT / task["run"], ROOT / task["indicator"]
    out = ROOT / task["output"] / "results"
    if unit == "file":
        text = (run / row["file"]).read_text()
        if hashlib.sha256(text.encode()).hexdigest() != row["source_sha256"]:
            raise ValueError("Source snapshot changed")
        cwd, dirs, message = file_audits.build_message(row, run, ind)
        file_audits.context.text = text
        file_audits.context.sources = Sources([cwd, *dirs.values()])
        validate = file_audits.validate
    else:
        cwd, dirs, message = judge.build_message(row, run, ind)
        validate = duplicates_judge.validate if task["audit"].startswith("duplicates") else duplicates_judge.original_validate
        duplicates_judge.context.sample = row
    try:
        result = backend.judge(row, ind, cwd, dirs, message, out, key, budget, validate)
        if unit == "file":
            result.update(unit="file", rubric=task["audit"], source_sha256=row["source_sha256"])
        backend.write_json(out / f"{row['id']}.json", result)
        return result
    finally:
        if unit == "file":
            del file_audits.context.text
            del file_audits.context.sources
        else:
            del duplicates_judge.context.sample


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prepare-only", action="store_true")
    parser.add_argument("--update-runner-only", action="store_true")
    parser.add_argument("--budget", default="20")
    parser.add_argument("--accept-harness-update", action="store_true")
    args = parser.parse_args()
    if args.update_runner_only:
        update_runner()
        return
    tasks = prepare(args.accept_harness_update)
    budget = backend.Budget(BASE / "budget.json", args.budget)
    if args.prepare_only:
        status("prepared", tasks, budget)
        print(f"Prepared {len(tasks)} matched judgments")
        return
    judge.judge_dirs = sources
    key = backend.api_key(Path.home() / ".secrets")
    failures = []
    with (BASE / "controller.log").open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        for task in tasks:
            if (ROOT / task["output"] / "results" / f"{task['row']['id']}.json").exists():
                continue
            done = status("running", tasks, budget, failures=failures,
                          current_audit=task["audit"], current_id=task["row"]["id"])
            while backend.PROVIDER == "DeepSeek" and (done >= 36 or float(budget.read()["billed_usd"]) >= 1) and not off_peak(datetime.datetime.now(datetime.timezone.utc)):
                status("waiting-for-off-peak", tasks, budget, failures=failures, resume_utc_hour=10)
                time.sleep(30)
            try:
                result = evaluate(task, key, budget)
                print(json.dumps({"audit": task["audit"], "id": task["row"]["id"],
                                  "verdict": result["verdict"], "cost_usd": result["cost_usd"]}), flush=True)
            except backend.BudgetExhausted:
                status("budget-complete", tasks, budget, failures=failures)
                return
            except backend.RateLimited:
                status("rate-limit-cooldown", tasks, budget)
                time.sleep(300)
                raise  # Stop admission after cooldown; never repeatedly hammer a limited endpoint.
            except Exception as error:
                failures.append({"audit": task["audit"], "id": task["row"]["id"], "error": str(error)})
                print(json.dumps({"failed": failures[-1]}), flush=True)
                status("failed", tasks, budget, failures=failures)
                backend.write_json(ROOT / task["output"] / "results" / f"{task['row']['id']}.failure.json", failures[-1])
                continue  # Preserve rejection and let other selected targets complete.
            (ROOT / task["output"] / "results" / f"{task['row']['id']}.failure.json").unlink(missing_ok=True)
            status("running", tasks, budget, failures=failures)
            time.sleep(10)
        done = status("running", tasks, budget, failures=failures)
        status("complete" if done == len(tasks) else "incomplete", tasks, budget, failures=failures)


if __name__ == "__main__":
    main()
