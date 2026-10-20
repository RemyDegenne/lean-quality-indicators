"""Run Sol 6.1, Luna 6 and Sonnet 5.5 on the original samples, then compare with Opus.

    python3 -u scripts/benchmark.py --jobs 12 --passes 2

Each model runs independently; --jobs is concurrency PER MODEL. Rerunning resumes
completed labels and samples. Calls use subscription authentication from the CLIs.
"""

import argparse
import json
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
MODELS = [("codex", "gpt-6.1-sol"), ("codex", "gpt-6-luna"), ("claude", "claude-sonnet-5-5")]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--jobs", type=int, default=12)
    parser.add_argument("--codex-jobs", type=int,
                        help="override concurrency per Codex model (defaults to --jobs)")
    parser.add_argument("--passes", type=int, default=2)
    parser.add_argument("--limit", type=int, default=300)
    args = parser.parse_args()
    if min(args.jobs, args.codex_jobs or args.jobs, args.passes, args.limit) < 1:
        parser.error("jobs, passes and limit must be positive")
    base = ROOT / "runs/main/unnecessary-hypotheses"
    labels = ["claude-opus-5-5-high", "rejudge-claude-opus-5-5-high"]
    labels += [f"{model}-high" + (f"-repeat-{n}" if n > 1 else "")
               for _, model in MODELS for n in range(1, args.passes + 1)]

    def run_model(backend, model):
        for n in range(1, args.passes + 1):
            label = f"{model}-high" + (f"-repeat-{n}" if n > 1 else "")
            cmd = [sys.executable, "-u", "scripts/judge.py", "--run", "main",
                   "--backend", backend, "--model", model, "--effort", "high",
                   "--label", label, "--limit", str(args.limit), "--jobs",
                   str((args.codex_jobs or args.jobs) if backend == "codex" else args.jobs)]
            print(f"Starting {label}", flush=True)
            log = base / f"{label}.log"
            with log.open("a") as output:
                result = subprocess.run(cmd, cwd=ROOT, stdout=output, stderr=subprocess.STDOUT)
            if result.returncode:
                raise RuntimeError(f"{label} failed; inspect {log} and rerun to resume")
            subprocess.run([sys.executable, "scripts/report.py", "--run", "main", "--label", label],
                           cwd=ROOT, check=True, capture_output=True)
            print(f"Finished {label}", flush=True)

    failed = []
    with ThreadPoolExecutor(max_workers=len(MODELS)) as executor:
        futures = {executor.submit(run_model, backend, model): model for backend, model in MODELS}
        for future in as_completed(futures):
            try:
                future.result()
            except Exception as exc:
                failed.append(str(exc))
                print(str(exc), file=sys.stderr, flush=True)
    if failed:
        raise SystemExit(1)
    subprocess.run([sys.executable, "scripts/compare.py", "--limit", str(args.limit),
                    "--labels", *labels, "--output", str(base / "model-comparison.md")],
                   cwd=ROOT, check=True)
    for _, model in MODELS:
        label = f"{model}-high"
        for first in labels[:2] + ([f"{label}-repeat-2"] if args.passes > 1 else []):
            subprocess.run([sys.executable, "scripts/agreement.py", "--run", "main",
                            "--first", first, "--second", label], cwd=ROOT,
                           check=True, capture_output=True)
            # agreement.py uses one output filename; preserve each comparison.
            source = base / label / "agreement-full.md"
            source.rename(base / label / f"agreement-vs-{first}.md")
    (base / "benchmark-complete.json").write_text(json.dumps({"labels": labels, "limit": args.limit},
                                                           indent=2) + "\n")
    print("All models complete; model-comparison.md written", flush=True)


if __name__ == "__main__":
    main()
