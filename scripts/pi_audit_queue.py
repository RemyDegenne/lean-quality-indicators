"""Run the small GLM theorem pilot before the file suite, waiting for API credits."""

import argparse
import datetime
import fcntl
import json
import os
from pathlib import Path
import shlex
import subprocess
import sys
import time
import urllib.request

ROOT = Path(__file__).resolve().parent.parent
BASE = ROOT / "runs/main/pi-glm-pilot"


def environment(path):
    env = os.environ.copy()
    for line in path.read_text().splitlines():
        parts = shlex.split(line, comments=True)
        if parts and parts[0] == "export":
            parts = parts[1:]
        for item in parts:
            if item.startswith("OPENROUTER_API_KEY="):
                env["OPENROUTER_API_KEY"] = item.split("=", 1)[1]
    if not env.get("OPENROUTER_API_KEY"):
        raise SystemExit("No OPENROUTER_API_KEY in credential file or environment")
    return env


def balance(env):
    request = urllib.request.Request("https://openrouter.ai/api/v1/credits",
                                    headers={"Authorization": "Bearer " + env["OPENROUTER_API_KEY"]})
    with urllib.request.urlopen(request, timeout=30) as response:
        data = json.load(response)["data"]
    return data["total_credits"] - data["total_usage"]


def status(stage, **extra):
    value = {"utc": datetime.datetime.now(datetime.timezone.utc).isoformat(timespec="seconds"),
             "pid": os.getpid(), "stage": stage, **extra}
    path = BASE / "status.json"
    tmp = path.with_suffix(".tmp")
    tmp.write_text(json.dumps(value, indent=2) + "\n")
    tmp.replace(path)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--secrets", type=Path, default=Path.home() / ".secrets")
    args = parser.parse_args()
    BASE.mkdir(parents=True, exist_ok=True)
    with (BASE / "controller.log").open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        commands = [
            ("theorem-pilot", [sys.executable, "-u", "scripts/pi_theorem_pilot.py", "--limit", "10"]),
            ("file-audits", [sys.executable, "-u", "scripts/file_audits.py", "--run", "file-quality-pilot-2026-10-21",
                             "--files-per-library", "10", "--backend", "pi", "--pi-provider", "openrouter",
                             "--model", "z-ai/glm-5.3", "--label", "glm-5.3-openrouter-pi-high", "--jobs", "1"]),
        ]
        for stage, command in commands:
            minimum = 0
            while True:
                env = environment(args.secrets)
                available = balance(env)
                if available <= minimum:
                    status("waiting-for-credits", next_stage=stage, available_usd=available)
                    time.sleep(30)
                    continue
                status(stage, command=command, available_usd=available)
                log_path = BASE / f"{stage}.log"
                with log_path.open("a") as log:
                    proc = subprocess.run(command, cwd=ROOT, env=env, stdout=log, stderr=subprocess.STDOUT)
                if proc.returncode == 0:
                    break
                tail = log_path.read_text()[-12000:]
                if "Insufficient credits" in tail or "insufficient credits" in tail:
                    minimum = max(0, balance(env))
                    status("waiting-for-credits", next_stage=stage, available_usd=minimum)
                    time.sleep(30)
                    continue
                status("failed", failed_stage=stage, returncode=proc.returncode, log=str(log_path))
                raise SystemExit(proc.returncode)
        status("complete", theorem_judgments=100, file_judgments=180)


if __name__ == "__main__":
    main()
