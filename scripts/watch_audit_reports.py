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


def save(path, value):
    temporary = path.with_name(path.name + f".{os.getpid()}.tmp")
    temporary.write_text(json.dumps(value, indent=2) + "\n")
    temporary.replace(path)


def supervise(info, status_path, command, log_path):
    status = json.loads(status_path.read_text()) if status_path.exists() else {}
    if status.get("stage") in ["complete", "budget-complete"]:
        return False
    try:
        finished, _ = os.waitpid(info["pid"], os.WNOHANG)
    except ChildProcessError:
        finished = 0
    if not finished:
        try:
            os.kill(info["pid"], 0)
            return True
        except ProcessLookupError:
            pass
    if info.get("automatic_restarts", 0) >= 2:
        status.update(stage="failed", reason="Automatic recovery limit reached; inspect worker log")
        save(status_path, status)
        return False
    if "restart_after" not in info:
        info["restart_after"] = time.time() + 300
    if time.time() < info["restart_after"]:
        status.update(stage="restart-wait", restart_after=info["restart_after"],
                      reason="Worker exited; bounded restart scheduled after cooldown")
        save(status_path, status)
        return True
    with log_path.open("a") as log:
        process = subprocess.Popen(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT,
                                   start_new_session=True)
    info.update(pid=process.pid, automatic_restarts=info.get("automatic_restarts", 0) + 1)
    info.pop("restart_after", None)
    status.update(stage="restarting", pid=process.pid)
    save(status_path, status)
    return True


def deepseek_health(base):
    """A live status snapshot from the request ledger, even within a long judgment."""
    status_path = base / "status.json"
    budget_path = base / "budget.json"
    if not status_path.exists() or not budget_path.exists():
        return
    status = json.loads(status_path.read_text())
    budget = json.loads(budget_path.read_text())
    requests = budget.get("requests", [])
    status.update(billed_usd=budget["billed_usd"],
                  request_spacing_seconds=budget.get("request_spacing_seconds", 10),
                  rate_limit_count=budget.get("rate_limit_count", 0),
                  request_count=len(requests),
                  unsettled_reservation_usd=sum(float(r["reserved_usd"]) for r in requests if r["billed_usd"] is None),
                  health_checked_epoch=time.time())
    if requests:
        status["latest_request_utc"] = requests[-1]["utc"]
        status["latest_request_target"] = requests[-1]["target"]
    if budget.get("not_before", 0) > time.time():
        status["cooldown_until_epoch"] = budget["not_before"]
    else:
        status.pop("cooldown_until_epoch", None)
    save(status_path, status)


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
                result = subprocess.run([sys.executable, str(ROOT / "scripts" / script)], cwd=ROOT)
                if result.returncode:
                    print(json.dumps({"report_refresh_failed": script, "exit_code": result.returncode}), flush=True)
            pilot = ROOT / "runs/openai-math-2026-10-21"
            launch = json.loads((pilot / "launch.json").read_text())
            active = False
            for name, info in launch.items():
                command = [sys.executable, "-u", "scripts/corpus_pilot.py", "judge", "--model", name,
                           "--limit", str(info.get("limit_per_audit", 100)), "--jobs", str(info.get("jobs", 1))]
                active |= supervise(info, pilot / f"{name}-status.json", command, Path(info["log"]))
            save(pilot / "launch.json", launch)
            deepseek = ROOT / "runs/deepseek-pilot-2026-10-21"
            if (deepseek / "launch.json").exists():
                info = json.loads((deepseek / "launch.json").read_text())
                active |= supervise(info, deepseek / "status.json",
                    [sys.executable, "-u", "scripts/deepseek_pilot.py"], deepseek / "worker.log")
                save(deepseek / "launch.json", info)
                deepseek_health(deepseek)
            if not active:
                return
            time.sleep(args.interval)


if __name__ == "__main__":
    main()
