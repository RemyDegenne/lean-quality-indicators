"""Refresh coverage, correlations and costs while the corpus pilots finish."""

import argparse
import fcntl
import json
import os
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent.parent


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--interval", type=int, default=300)
    args = parser.parse_args()
    if args.interval < 60:
        parser.error("Refresh no more often than once a minute")
    with (ROOT / "runs/main/audit-reports-lock.log").open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        while True:
            for script in ["audit_dashboard.py", "api_costs.py", "order_model_tables.py"]:
                subprocess.run([sys.executable, str(ROOT / "scripts" / script)], cwd=ROOT, check=True)
            pilot = ROOT / "runs/openai-math-2026-10-21"
            launch = json.loads((pilot / "launch.json").read_text())
            active = False
            for name, info in launch.items():
                path = pilot / f"{name}-status.json"
                status = json.loads(path.read_text()) if path.exists() else {}
                if status.get("stage") in ["complete", "failed"]:
                    continue
                try:
                    os.kill(info["pid"], 0)
                    active = True
                except ProcessLookupError:
                    status.update(stage="failed", reason="Worker exited; inspect its local log")
                    path.write_text(json.dumps(status, indent=2) + "\n")
            if not active:
                return
            time.sleep(args.interval)


if __name__ == "__main__":
    main()
