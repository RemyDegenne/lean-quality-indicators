"""Refresh coverage, correlations and costs while Luna and GLM audits finish."""

import argparse
import fcntl
import json
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
            for script in ["audit_dashboard.py", "api_costs.py"]:
                subprocess.run([sys.executable, str(ROOT / "scripts" / script)], cwd=ROOT, check=True)
            glm = json.loads((ROOT / "runs/main/pi-glm-pilot/status.json").read_text())
            luna = json.loads((ROOT / "runs/file-quality-pilot-2026-10-21/reports/gpt-6-luna-high/status.json").read_text())
            if glm["stage"] in ["complete", "failed"] and (luna.get("complete") or luna.get("failed")):
                return
            time.sleep(args.interval)


if __name__ == "__main__":
    main()
