"""Wait for an existing file-audit controller, then extend its selected rubrics.

The runtime must contain the original runner matching saved protocol hashes.
Only rejected missing-path citations are retried, at most three times.
"""

import argparse
import fcntl
import json
from pathlib import Path
import subprocess
import sys
import time


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--runtime", required=True, type=Path)
    parser.add_argument("--run", required=True)
    parser.add_argument("--model", required=True)
    args = parser.parse_args()
    label = f"{args.model}-high"
    run = args.runtime / "runs" / args.run
    # Wait without competing for an active model session. The child takes this lock.
    with (run / f"{label}-runner.log").open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
    command = [sys.executable, "-u", "scripts/reproduce_file_audits.py",
               "--run", args.run, "--files-per-library", "10", "--model", args.model,
               "--backend", "codex", "--jobs", "1"]
    report = run / "reports" / label
    (report / "complete.json").unlink(missing_ok=True)
    for attempt in range(4):
        result = subprocess.run(command, cwd=args.runtime)
        if result.returncode == 0:
            return
        status = json.loads((report / "status.json").read_text())
        errors = status.get("failed", [])
        if attempt == 3 or not errors or not all(
                "[Errno 2] No such file or directory" in error["error"] for error in errors):
            raise SystemExit(result.returncode)
        print("Rejected citation; resuming unchanged protocol in 60 seconds", flush=True)
        time.sleep(60)


if __name__ == "__main__":
    main()
