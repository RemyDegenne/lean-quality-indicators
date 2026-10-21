"""Run an indicator's judge on the samples of a run.

    python3 scripts/judge.py --run pilot --indicator unnecessary-hypotheses \
        [--model claude-opus-5-5] [--effort high] [--jobs 4] [--libs ...] [--ids ...] [--limit K]

Each sample is sent, on its own, to a fresh headless `claude -p` session (or `codex exec`
with --backend codex) with the indicator's
prompt.md as system prompt and its schema.json as structured-output schema, and without
project or user customisations (`--safe-mode`). The session runs in the pinned clone of the
sample's library, with the read-only tools Read, Grep and Glob, and can also read the Mathlib
clone (master), the Lean core sources of the library's toolchain, and, for Formal Frontier,
the other Formal Frontier repositories (they depend on one another).

Results go to runs/<run>/<indicator>/<label>/results/<id>.json (label defaults to
<model>-<effort>, so several judges can be compared on one sample); the raw `claude -p`
output is kept next to it as <id>.raw.json. Samples that already have a result are skipped,
so an interrupted run can be resumed by running the same command again.

    python3 scripts/judge.py --run main --export DIR

writes, instead of judging, what each judge session receives, for running the same protocol
with another agent: DIR/system-prompt.md, DIR/schema.json, DIR/messages/<id>.md and
DIR/jobs.jsonl (one line per sample: id, library, message file, working directory, other
readable directories).
"""

from __future__ import annotations

import argparse
import datetime
import itertools
import json
import os
import subprocess
import sys
import threading
import hashlib
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import fetch  # noqa: E402
import indicator  # noqa: E402
import codex_judge  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent
REPOS = ROOT / "repos"


def validate_verdict(verdict: dict, ind: Path) -> None:
    """Check the indicator's schema subset and the hypothesis verdict invariant."""
    def check(value, schema):
        expected = {"object": dict, "array": list, "string": str, "boolean": bool}
        if not isinstance(value, expected[schema["type"]]):
            raise ValueError(f"Expected {schema['type']}")
        if "enum" in schema and value not in schema["enum"]:
            raise ValueError(f"Unexpected enum value: {value}")
        if schema["type"] == "object":
            if not set(schema.get("required", [])) <= value.keys():
                raise ValueError("Missing required fields")
            if schema.get("additionalProperties") is False and value.keys() - schema["properties"].keys():
                raise ValueError("Unexpected fields")
            for key, val in value.items():
                if key in schema["properties"]:
                    check(val, schema["properties"][key])
        elif schema["type"] == "array":
            for item in value:
                check(item, schema["items"])
    check(verdict, json.loads((ind / "schema.json").read_text()))
    if "hypotheses" in verdict and bool(verdict["hypotheses"]) != \
            (verdict["verdict"] == "unnecessary_hypothesis_found"):
        raise ValueError("Hypotheses disagree with the verdict")


def select_samples(samples: list[dict], args) -> list[dict]:
    if args.libs:
        samples = [s for s in samples if s["lib"] in args.libs.split(",")]
    if args.ids:
        samples = [s for s in samples if s["id"] in args.ids.split(",")]
    if args.limit is not None:
        per: dict[str, int] = {}
        kept = []
        for s in samples:
            per[s["lib"]] = per.get(s["lib"], 0) + 1
            if per[s["lib"]] <= args.limit:
                kept.append(s)
        samples = kept
    return samples


def judge_dirs(sample: dict, mathlib: str = "master") -> tuple[Path, dict[str, Path]]:
    """Working directory of the judge, and the other directories it may read.

    `mathlib` is "master" (the Mathlib clone) or "pinned" (the Mathlib and Batteries versions
    the sample's repository pins, cloned by `fetch.py --deps`)."""
    repo = REPOS / sample["dir"]
    dirs = {}
    if sample["lib"] == "formal-frontier":
        dirs["the other Formal Frontier libraries"] = REPOS / "formal-frontier"
    if mathlib == "pinned":
        for name, (_, rev) in sorted(fetch.pinned_deps(sample["dir"]).items(), reverse=True):
            d = fetch.dep_dir(name, rev)
            if not d.is_dir():
                raise SystemExit(f"{d} is missing: run `python3 scripts/fetch.py --deps`")
            label = "Mathlib" if name == "mathlib" else "Batteries"
            dirs[f"{label} (the version this library depends on, commit {rev[:12]})"] = d
    elif sample["lib"] != "mathlib":
        dirs["Mathlib (current master, possibly newer than the version the library uses)"] = \
            REPOS / "mathlib"
    toolchain = (repo / "lean-toolchain").read_text().strip()
    core = (Path.home() / ".elan" / "toolchains" /
            toolchain.replace("/", "--").replace(":", "---") / "src" / "lean")
    if core.is_dir():
        dirs[f"Lean core ({toolchain})"] = core
    return repo, dirs


def build_message(sample: dict, run: Path, ind: Path,
                  extra: dict[str, str] | None = None) -> tuple[Path, dict[str, Path], str]:
    """Working directory, readable directories and user message of one judge session;
    `extra` fills further `{placeholders}` of the indicator's message.md."""
    cwd, dirs = judge_dirs(sample, indicator.config(ind)["mathlib"])
    message = (ind / "message.md").read_text()
    for key, val in {
        "{snippet}": (run / sample["file"]).read_text().rstrip("\n"),
        "{name}": sample["name"], "{line}": str(sample["line"]), "{path}": sample["path"],
        "{dirs}": "\n".join(f"- {k}: `{v}`" for k, v in dirs.items()),
        **(extra or {}),
    }.items():
        message = message.replace(key, val)
    return cwd, dirs, message


def judge_one(sample: dict, run: Path, ind: Path, out: Path, args,
              extra: dict[str, str] | None = None) -> dict:
    """Run the judge of indicator directory `ind` on one sample."""
    cwd, dirs, message = build_message(sample, run, ind, extra)
    if getattr(args, "backend", "claude") == "codex":
        return codex_judge.judge(sample, ind, out, args, cwd, dirs, message)
    cmd = [args.claude, "-p", "--model", args.model, "--effort", args.effort,
           "--tools", "Read,Grep,Glob", "--permission-mode", "dontAsk",
           "--safe-mode", "--restricted", "--no-session-persistence",
           "--system-prompt-file", str(ind / "prompt.md"),
           "--json-schema", (ind / "schema.json").read_text(),
           "--max-budget-usd", str(args.max_budget),
           "--output-format", "stream-json", "--verbose"]
    for d in dirs.values():
        cmd += ["--add-dir", str(d)]
    last_err = None
    first_attempt = codex_judge.next_attempt(out, sample["id"])
    for attempt in range(first_attempt, first_attempt + args.retries + 1):
        try:
            p = codex_judge.run_process(cmd, message, cwd, args.timeout)
        except subprocess.TimeoutExpired:
            last_err = f"timeout after {args.timeout}s"
            continue
        (out / f"{sample['id']}.attempt-{attempt}.transcript.jsonl").write_text(p.stdout)
        (out / f"{sample['id']}.attempt-{attempt}.stderr.log").write_text(p.stderr)
        events = []
        for line in p.stdout.splitlines():
            try:
                events.append(json.loads(line))
            except json.JSONDecodeError:
                pass
        raw = next((e for e in reversed(events) if e.get("type") == "result"), None)
        if raw is None:
            last_err = f"exit {p.returncode}: {p.stdout[-500:]} {p.stderr[-500:]}"
            continue
        verdict = raw.get("structured_output")
        if p.returncode or raw.get("is_error") or not isinstance(verdict, dict):
            last_err = f"{raw.get('subtype')}: {str(raw.get('result'))[:500]}"
            continue
        try:
            validate_verdict(verdict, ind)
        except (ValueError, KeyError, TypeError) as exc:
            last_err = f"Invalid verdict: {exc}"
            continue
        # Full session (tool calls and their results), for auditing the judge.
        (out / f"{sample['id']}.transcript.jsonl").write_text(p.stdout)
        (out / f"{sample['id']}.raw.json").write_text(json.dumps(raw, indent=1) + "\n")
        res = {"id": sample["id"], "lib": sample["lib"], **verdict,
               "model": args.model, "effort": args.effort,
               "backend": "claude", "usage": raw.get("usage"),
               "cost_usd": raw.get("total_cost_usd"), "duration_ms": raw.get("duration_ms"),
               "turns": raw.get("num_turns"), "attempts": attempt,
               "judged": datetime.datetime.now().isoformat(timespec="seconds")}
        destination = out / f"{sample['id']}.json"
        temporary = destination.with_suffix(".tmp")
        temporary.write_text(json.dumps(res, indent=1, ensure_ascii=False) + "\n")
        temporary.replace(destination)
        return res
    raise RuntimeError(last_err)


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--run", required=True)
    ap.add_argument("--indicator", default="unnecessary-hypotheses")
    ap.add_argument("--model", default="claude-opus-5-5")
    ap.add_argument("--backend", choices=["claude", "codex"], default="claude")
    ap.add_argument("--codex", default=os.environ.get("CODEX_BIN", "codex"))
    ap.add_argument("--effort", default="high", choices=["low", "medium", "high", "xhigh", "max"])
    ap.add_argument("--label", help="results subdirectory (default: <model>-<effort>)")
    ap.add_argument("--jobs", type=int, default=4, help="parallel judge sessions")
    ap.add_argument("--libs", help="comma-separated library ids")
    ap.add_argument("--ids", help="comma-separated sample ids")
    ap.add_argument("--limit", type=int, help="judge at most this many samples per library")
    ap.add_argument("--retries", type=int, default=2)
    ap.add_argument("--timeout", type=int, default=1800, help="seconds per judge call")
    ap.add_argument("--max-budget", type=float, default=5.0, help="USD cap per judge call")
    ap.add_argument("--claude", default=os.environ.get("CLAUDE_BIN", "claude"),
                    help="Claude Code executable (default: $CLAUDE_BIN, else `claude`)")
    ap.add_argument("--order", choices=["interleave", "file"], default="interleave",
                    help="interleave: one sample of each library in turn, so that progress is "
                         "even across libraries (default); file: the order of samples.jsonl")
    ap.add_argument("--export", metavar="DIR",
                    help="write the judge inputs to DIR instead of judging")
    args = ap.parse_args()
    if args.jobs < 1 or (args.limit is not None and args.limit < 1):
        ap.error("--jobs and --limit must be positive")

    run = ROOT / "runs" / args.run
    ind = ROOT / "indicators" / args.indicator
    skip = indicator.config(ind)["skip_libraries"]
    samples = [s for s in map(json.loads, (run / "samples.jsonl").open()) if s["lib"] not in skip]
    samples = select_samples(samples, args)
    if args.export:
        exp = Path(args.export)
        (exp / "messages").mkdir(parents=True, exist_ok=True)
        (exp / "system-prompt.md").write_text((ind / "prompt.md").read_text())
        (exp / "schema.json").write_text((ind / "schema.json").read_text())
        with (exp / "jobs.jsonl").open("w") as f:
            for s in samples:
                cwd, dirs, message = build_message(s, run, ind)
                (exp / "messages" / f"{s['id']}.md").write_text(message)
                f.write(json.dumps({"id": s["id"], "lib": s["lib"],
                                    "message": f"messages/{s['id']}.md", "cwd": str(cwd),
                                    "read_dirs": [str(d) for d in dirs.values()]}) + "\n")
        print(f"exported {len(samples)} judge inputs to {exp}")
        return
    out = run / args.indicator / (args.label or f"{args.model}-{args.effort}") / "results"
    out.mkdir(parents=True, exist_ok=True)
    manifest = {"backend": args.backend, "model": args.model, "effort": args.effort,
                "indicator": args.indicator,
                "runner_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                "backend_sha256": hashlib.sha256(Path(codex_judge.__file__).read_bytes()).hexdigest(),
                "source_tools_sha256": hashlib.sha256(
                    Path(__file__).with_name("source_tools.py").read_bytes()).hexdigest(),
                "prompt_sha256": hashlib.sha256((ind / "prompt.md").read_bytes()).hexdigest(),
                "schema_sha256": hashlib.sha256((ind / "schema.json").read_bytes()).hexdigest(),
                "corpus_sha256": hashlib.sha256((ROOT / "libraries.lock.json").read_bytes()).hexdigest()}
    manifest_path = out.parent / "judge.json"
    if manifest_path.exists() and json.loads(manifest_path.read_text())["protocol"] != manifest:
        ap.error("This label already uses a different judge protocol; choose a new --label")
    if not manifest_path.exists():
        executable = args.codex if args.backend == "codex" else args.claude
        version = subprocess.run([executable, "--version"], capture_output=True, text=True, check=True)
        manifest_path.write_text(json.dumps({"protocol": manifest, "cli_version": version.stdout.strip(),
                                            "argv": sys.argv[1:],
            "sample_ids": [s["id"] for s in samples]}, indent=2) + "\n")
    todo = [s for s in samples if not (out / f"{s['id']}.json").exists()]
    if args.order == "interleave":
        by_lib: dict[str, list[dict]] = {}
        for s in todo:
            by_lib.setdefault(s["lib"], []).append(s)
        todo = [s for group in itertools.zip_longest(*by_lib.values()) for s in group if s]
    print(f"{len(samples) - len(todo)} already judged, {len(todo)} to go -> {out}")

    lock = threading.Lock()
    done = cost = 0.0
    failed = []
    with ThreadPoolExecutor(args.jobs) as ex:
        futs = {ex.submit(judge_one, s, run, ind, out, args): s for s in todo}
        for f in as_completed(futs):
            s = futs[f]
            with lock:
                done += 1
                try:
                    r = f.result()
                    cost += r.get("cost_usd") or 0
                    flag = "FOUND" if r["verdict"] == "unnecessary_hypothesis_found" else \
                        "none" if r["verdict"] in ("none_found", "none") else r["verdict"]
                    cost_text = f"${cost:.2f} total" if args.backend == "claude" else "tokens recorded"
                    print(f"[{int(done)}/{len(todo)}] {s['id']:24} {flag:6} "
                          f"{cost_text}", flush=True)
                except Exception as e:  # noqa: BLE001
                    failed.append(s["id"])
                    (out.parent / "errors.log").open("a").write(f"{s['id']}\t{e}\n")
                    print(f"[{int(done)}/{len(todo)}] {s['id']:24} ERROR {e}", flush=True)
    if failed:
        print(f"{len(failed)} failed (see errors.log); rerun the same command to retry them",
              file=sys.stderr)
        raise SystemExit(1)


if __name__ == "__main__":
    main()
