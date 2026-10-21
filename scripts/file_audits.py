"""Sample whole Lean files and run independent, versioned quality rubrics.

python3 -u scripts/file_audits.py --run file-quality-pilot-2026-10-21 \
    --files-per-library 10 --model claude-sonnet-5-5 --jobs 2

The same files are used for every rubric. A fresh session reviews one file against
one rubric. Increasing --files-per-library extends the deterministic sample;
another --model or --label keeps its judgments separate. Sources are read only.
"""

import argparse
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED
import datetime
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import threading

import fetch
import judge
import leanscan
import sample as theorem_sample
from source_tools import Sources

ROOT = Path(__file__).resolve().parent.parent
SUITE = ROOT / "audits/file-quality-v1"
RUBRICS = ["concept-reinvention", "statement-generality", "vacuity-and-misstatement",
           "simp-interface",
           "repeated-proof-machinery", "readable-proof-simplification"]
MATHEMATICS = re.compile(r"(?m)^(?:(?:public|noncomputable|private|protected|local|scoped|unsafe)\s+)*"
                         r"(?:theorem|lemma|def|abbrev|structure|class|inductive|instance|opaque)\b")
context = threading.local()
original_build_message = judge.build_message


def digest(value):
    return hashlib.sha256(value).hexdigest()


def utc():
    return datetime.datetime.now(datetime.timezone.utc).isoformat(timespec="seconds")


def write_json(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(".tmp")
    temporary.write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n")
    temporary.replace(path)


def check_schema(value, schema):
    expected = {"object": dict, "array": list, "string": str, "integer": int}
    if type(value) is not expected[schema["type"]]:
        raise ValueError(f"Expected {schema['type']}")
    if "enum" in schema and value not in schema["enum"]:
        raise ValueError("Unexpected verdict or coverage")
    if isinstance(value, dict):
        if set(value) != set(schema["required"]):
            raise ValueError("Missing or unexpected fields")
        for key, val in value.items():
            check_schema(val, schema["properties"][key])
    elif isinstance(value, list):
        if not schema.get("minItems", 0) <= len(value) <= schema.get("maxItems", 10**6):
            raise ValueError("Wrong number of findings or evidence items")
        for item in value:
            check_schema(item, schema["items"])


def normalise(text):
    return " ".join(text.split())


def validate(verdict, ind):
    check_schema(verdict, json.loads((ind / "schema.json").read_text()))
    if bool(verdict["findings"]) != (verdict["verdict"] == "findings_found"):
        raise ValueError("Findings disagree with verdict")
    if not verdict["review_notes"].strip():
        raise ValueError("Review notes are required")
    lines = context.text.splitlines()
    for finding in verdict["findings"]:
        start, end = finding["start_line"], finding["end_line"]
        if not 1 <= start <= end <= len(lines):
            raise ValueError("Finding outside target file")
        excerpt = normalise(finding["excerpt"])
        if not excerpt or excerpt not in normalise("\n".join(lines[start-1:end])):
            raise ValueError("Finding excerpt is not in its stated target line range")
        for key in ["declaration", "problem", "proposed_change", "benefit"]:
            if not finding[key].strip():
                raise ValueError(f"Finding needs {key}")
        for evidence in finding["evidence"]:
            if not Path(evidence["path"]).is_absolute():
                raise ValueError("Evidence needs an absolute source path")
            source = context.sources.path(evidence["path"])
            quotation = normalise(evidence["excerpt"])
            if not quotation or quotation not in normalise(source.read_text()):
                raise ValueError("Evidence quotation not found in cited source")


def prepare(run, n, seed, libraries):
    cfg, lock = theorem_sample.load_config()
    contract = {"suite": "file-quality-v1", "unit": "file", "seed": seed, "libraries": libraries,
                "corpus_sha256": digest((ROOT / "libraries.lock.json").read_bytes()),
                "source_config_sha256": digest((ROOT / "libraries.toml").read_bytes()),
                "selection": "SHA256 ordering, then mathematical declaration filter on masked source",
                "populations": {}}
    rows, texts = [], {}
    for lib_id in libraries:
        lib = next(lib for lib in cfg["library"] if lib["id"] == lib_id)
        candidates = [(src, rel) for src in lib["source"]
                      for rel in theorem_sample.source_files(cfg.get("defaults", {}), src)]
        population = sorted((src["dir"], rel) for src, rel in candidates)
        contract["populations"][lib_id] = {"candidate_files": len(population),
                                         "sha256": digest(json.dumps(population).encode())}
        for src in lib["source"]:
            actual = fetch.git("rev-parse", "HEAD", cwd=ROOT / "repos" / src["dir"])
            if actual != lock[src["dir"]]["commit"]:
                raise ValueError(f"Source checkout moved: {src['dir']}")
        candidates.sort(key=lambda pair: digest(
            f"file-quality-v1:{seed}:{lib_id}:{pair[0]['dir']}:{pair[1]}".encode()))
        chosen = 0
        for src, rel in candidates:
            data = (ROOT / "repos" / src["dir"] / rel).read_bytes()
            text = data.decode("utf-8")
            if not MATHEMATICS.search(leanscan.mask(text)[0]):
                continue
            sid = f"{lib_id}-file-{chosen:04d}"
            commit = lock[src["dir"]]["commit"]
            row = {"id": sid, "lib": lib_id, "dir": src["dir"], "path": rel,
                   "name": rel, "line": 1, "end_line": len(text.splitlines()), "unit": "file",
                   "commit": commit, "source_sha256": digest(data), "source_bytes": len(data),
                   "url": f"{src['url']}/blob/{commit}/{rel}", "file": f"files/{lib_id}/{rel}"}
            rows.append(row)
            texts[sid] = data
            chosen += 1
            if chosen == n:
                break
        if chosen < n:
            raise ValueError(f"Only {chosen} eligible files in {lib_id}")
    run.mkdir(parents=True, exist_ok=True)
    manifest = run / "run.json"
    if manifest.exists() and json.loads(manifest.read_text())["contract"] != contract:
        raise ValueError("Existing run has a different corpus or sampling contract")
    samples_path = run / "samples.jsonl"
    if samples_path.exists():
        by_id = {row["id"]: row for row in rows}
        for old in map(json.loads, samples_path.read_text().splitlines()):
            if by_id.get(old["id"]) != old:
                raise ValueError("Cannot shrink or change an existing file sample")
    for row in rows:
        target = run / row["file"]
        target.parent.mkdir(parents=True, exist_ok=True)
        if target.exists() and target.read_bytes() != texts[row["id"]]:
            raise ValueError(f"Saved source snapshot changed: {row['id']}")
        target.write_bytes(texts[row["id"]])
    samples_path.write_text("".join(json.dumps(row, ensure_ascii=False) + "\n" for row in rows))
    write_json(manifest, {"contract": contract, "files_per_library": n,
                          "total_files": len(rows), "updated_utc": utc()})
    shutil.copyfile(ROOT / "libraries.lock.json", run / "corpus-lock.json")
    for rubric in RUBRICS:
        ind = run / "protocols" / rubric
        ind.mkdir(parents=True, exist_ok=True)
        artifacts = {"prompt.md": (SUITE / "common.md").read_bytes() + b"\n" +
                     (SUITE / "rubrics" / f"{rubric}.md").read_bytes(),
                     "schema.json": (SUITE / "schema.json").read_bytes(),
                     "message.md": (SUITE / "message.md").read_bytes(),
                     "config.toml": b'mathlib = "pinned"\npositive = ["findings_found"]\n'}
        for name, data in artifacts.items():
            path = ind / name
            if path.exists() and path.read_bytes() != data:
                raise ValueError("Rubric changed; use a new run for a different protocol version")
            path.write_bytes(data)
    return rows, contract


def build_message(row, run, ind, extra=None):
    return original_build_message(row, run, ind, {"{end_line}": str(row["end_line"]), **(extra or {})})


def review(row, rubric, run, label, args):
    ind = run / "protocols" / rubric
    out = run / rubric / label / "results"
    context.text = (run / row["file"]).read_text()
    if digest(context.text.encode()) != row["source_sha256"]:
        raise ValueError("Target snapshot hash changed")
    cwd, dirs = judge.judge_dirs(row, "pinned")
    if digest((cwd / row["path"]).read_bytes()) != row["source_sha256"]:
        raise ValueError("Target source changed")
    context.sources = Sources([cwd, *dirs.values()])
    try:
        result = judge.judge_one(row, run, ind, out, args)
        result.update(unit="file", source_sha256=row["source_sha256"], rubric=rubric)
        write_json(out / f"{row['id']}.json", result)
        return result
    finally:
        del context.text
        del context.sources


def report(run, rows, label):
    names = {"mathlib": "Mathlib", "tauceti": "Tau Ceti", "lean-pool": "Lean Pool"}
    lines = ["# File quality pilot", "", f"Judge: `{label}`. Unit: one complete source file.", "",
             "Cells: files with findings / completed reviews (number of findings). "
             "The same files are used for every rubric.", "",
             "| Rubric | " + " | ".join(names.values()) + " |", "|---|---:|---:|---:|"]
    detail = []
    complete, count = True, 0
    for rubric in RUBRICS:
        cells = []
        for lib in names:
            found = []
            expected = [row for row in rows if row["lib"] == lib]
            for row in expected:
                path = run / rubric / label / "results" / f"{row['id']}.json"
                if not path.exists():
                    complete = False
                    continue
                result = json.loads(path.read_text())
                found.append(result)
                count += 1
                for finding in result["findings"]:
                    url = row["url"] + f"#L{finding['start_line']}-L{finding['end_line']}"
                    evidence = "\n".join(f"- `{e['declaration']}` in `{e['path']}`: {e['excerpt']}"
                                         for e in finding["evidence"])
                    detail += [f"### {rubric}: [{row['path']}]({url})", "",
                               f"Declaration: `{finding['declaration']}`", "",
                               finding["problem"], "", "Proposed change:", "", finding["proposed_change"], "",
                               "Benefit: " + finding["benefit"], "", "Source evidence:", "", evidence, ""]
            flagged = sum(bool(r["findings"]) for r in found)
            findings = sum(len(r["findings"]) for r in found)
            partial = sum(r["coverage"] == "partial" for r in found)
            na = sum(r["verdict"] == "not_applicable" for r in found)
            cells.append(f"{flagged}/{len(found)} ({findings})" + (f"; {partial} partial" if partial else "") +
                         (f"; {na} N/A" if na else ""))
        lines.append("| " + rubric + " | " + " | ".join(cells) + " |")
    lines += ["", f"Completed judgments: {count}/{len(rows)*len(RUBRICS)}.", "",
              "Flags are judge claims; replacements have not been compiled or independently audited. "
              "This small file sample does not estimate a theorem defect rate. Rubrics may flag the same issue.", ""]
    destination = run / "reports" / label
    destination.mkdir(parents=True, exist_ok=True)
    (destination / "summary.md").write_text("\n".join(lines).rstrip() + "\n")
    (destination / "findings.md").write_text("# Findings\n\n" + "\n".join(detail).rstrip() + "\n")
    return complete, count


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--run", required=True)
    parser.add_argument("--files-per-library", type=int, default=10)
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--model", default="claude-sonnet-5-5")
    parser.add_argument("--backend", choices=["claude", "codex"], default="claude")
    parser.add_argument("--label")
    parser.add_argument("--effort", default="high")
    parser.add_argument("--jobs", type=int, default=2)
    parser.add_argument("--rubrics", help="comma-separated subset; default all rubrics")
    parser.add_argument("--prepare-only", action="store_true")
    parser.add_argument("--report-only", action="store_true")
    parser.add_argument("--timeout", type=int, default=1800)
    parser.add_argument("--retries", type=int, default=2)
    parser.add_argument("--max-budget", type=float, default=5)
    parser.add_argument("--claude", default=os.environ.get("CLAUDE_BIN", "claude"))
    parser.add_argument("--codex", default=str(ROOT / "scripts/codex_rate_guard.py"))
    args = parser.parse_args()
    if args.jobs < 1 or args.files_per_library < 1 or Path(args.run).name != args.run:
        parser.error("Use positive jobs and file count, and a simple run directory name")
    rubrics = args.rubrics.split(",") if args.rubrics else RUBRICS
    if not set(rubrics) <= set(RUBRICS):
        parser.error("Unknown rubric")
    run = ROOT / "runs" / args.run
    run.mkdir(parents=True, exist_ok=True)
    label = args.label or f"{args.model}-{args.effort}"
    if Path(label).name != label:
        parser.error("Use a simple label directory name")
    lock = (run / f"{label}-runner.log").open("a")
    fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    rows, contract = prepare(run, args.files_per_library, args.seed, ["mathlib", "tauceti", "lean-pool"])
    print(f"Prepared {len(rows)} files, {len(RUBRICS)} rubrics", flush=True)
    if args.prepare_only:
        return
    if args.report_only:
        report(run, rows, label)
        return
    judge.validate_verdict = validate
    judge.build_message = build_message
    executable = args.claude if args.backend == "claude" else args.codex
    version = subprocess.run([executable, "--version"], capture_output=True, text=True, check=True).stdout.strip()
    code_hashes = {name: digest((ROOT / "scripts" / name).read_bytes()) for name in
                   ["file_audits.py", "judge.py", "codex_judge.py", "source_tools.py", "leanscan.py", "sample.py"]}
    for rubric in rubrics:
        ind = run / "protocols" / rubric
        directory = run / rubric / label
        (directory / "results").mkdir(parents=True, exist_ok=True)
        protocol = {"backend": args.backend, "model": args.model, "effort": args.effort,
                    "unit": "file", "rubric": rubric, "contract": contract, "code_hashes": code_hashes,
                    "artifacts": {p.name: digest(p.read_bytes()) for p in ind.iterdir()}}
        path = directory / "judge.json"
        manifest = json.loads(path.read_text()) if path.exists() else {
            "protocol": protocol, "cli_version": version, "selections": []}
        if manifest["protocol"] != protocol:
            raise ValueError("Judge protocol changed; choose a new label or experiment")
        manifest["selections"].append({"utc": utc(), "sample_ids": [r["id"] for r in rows],
                                      "samples_sha256": digest((run / "samples.jsonl").read_bytes())})
        write_json(path, manifest)
        for row in rows:
            build_message(row, run, ind)  # Preflight every source root before launching sessions.
    libraries = contract["libraries"]
    by_lib = {lib: [row for row in rows if row["lib"] == lib] for lib in libraries}
    tasks = [(by_lib[lib][i], rubric) for i in range(args.files_per_library)
             for rubric in rubrics for lib in libraries]
    tasks = iter((row, rubric) for row, rubric in tasks
                 if not (run / rubric / label / "results" / f"{row['id']}.json").exists())
    failed, pending = [], {}
    status_path = run / "reports" / label / "status.json"
    with ThreadPoolExecutor(args.jobs) as pool:
        exhausted = False
        while True:
            while not failed and not exhausted and len(pending) < args.jobs:
                task = next(tasks, None)
                if task is None:
                    exhausted = True
                    break
                row, rubric = task
                pending[pool.submit(review, row, rubric, run, label, args)] = task
            if not pending:
                break
            finished, _ = wait(pending, timeout=30, return_when=FIRST_COMPLETED)
            for future in finished:
                row, rubric = pending.pop(future)
                try:
                    result = future.result()
                    print(json.dumps({"utc": utc(), "id": row["id"], "rubric": rubric,
                                      "verdict": result["verdict"], "findings": len(result["findings"])}), flush=True)
                except Exception as exc:
                    failed.append({"id": row["id"], "rubric": rubric, "error": str(exc)})
                    print(json.dumps({"error": failed[-1]}), flush=True)
            complete, count = report(run, rows, label)
            write_json(status_path, {"utc": utc(), "pid": os.getpid(), "completed": count,
                                     "expected": len(rows)*len(RUBRICS), "active": len(pending),
                                     "failed": failed, "complete": complete})
    complete, count = report(run, rows, label)
    if failed:
        raise SystemExit("Audit stopped after a failed judgment; inspect status and resume the same command")
    if complete:
        write_json(run / "reports" / label / "complete.json", {"utc": utc(), "judgments": count})
    print(f"Finished selected rubrics: {count}/{len(rows)*len(RUBRICS)} judgments", flush=True)


if __name__ == "__main__":
    main()
