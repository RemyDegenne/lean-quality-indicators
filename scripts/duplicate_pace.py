#!/usr/bin/env python3
"""Pace duplicate sessions until the hypothesis benchmark completes.

The Codex executable behind this wrapper remains the shared 429 rate guard.
Pacing applies to all retries and is shared by the workers for each model.
"""

import contextlib
import fcntl
import json
import os
from pathlib import Path
import subprocess
import sys
import time

from codex_rate_guard import alive

BASE = Path(__file__).resolve().parent.parent / "runs/main/duplicates-mathlib-inclusive"
GATE = BASE.parent / "unnecessary-hypotheses/benchmark-complete.json"


@contextlib.contextmanager
def transaction():
    BASE.mkdir(parents=True, exist_ok=True)
    with (BASE / "pace-lock.log").open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        path = BASE / "pace-state.log"
        state = json.loads(path.read_text()) if path.exists() else {"active": {}, "queue": {}, "next": {}}
        for key in ["active", "queue"]:
            state[key] = {pid: row for pid, row in state[key].items() if alive(pid)}
        yield state
        temporary = BASE / "pace-pending.log"
        temporary.write_text(json.dumps(state) + "\n")
        temporary.replace(path)


def admit(pid, model, spacing):
    with transaction() as state:
        now = time.time()
        state["queue"].setdefault(pid, {"model": model, "time": now})
        slow = not GATE.exists()
        peers = [p for p, row in state["queue"].items() if row["model"] == model]
        first = min(peers, key=lambda p: state["queue"][p]["time"])
        busy = any(row["model"] == model for row in state["active"].values())
        if slow and (busy or now < state["next"].get(model, 0) or first != pid):
            return False
        state["queue"].pop(pid)
        state["active"][pid] = {"model": model, "started": now}
        state["next"][model] = now + spacing
        with (BASE / "pace-events.log").open("a") as output:
            output.write(json.dumps({"time": now, "model": model, "pid": pid,
                                     "phase": "slow" if slow else "full"}) + "\n")
        return True


def main():
    real = os.environ["DUPLICATE_REAL_BIN"]
    if "--version" in sys.argv or "--help" in sys.argv:
        return subprocess.call([real, *sys.argv[1:]])
    model = sys.argv[sys.argv.index("--model") + 1]
    pid = str(os.getpid())
    spacing = float(os.environ.get("DUPLICATE_SLOW_SPACING", "180"))
    while not admit(pid, model, spacing):
        time.sleep(2)
    try:
        # Inherit stdin, stdout and stderr verbatim, including structured output.
        return subprocess.call([real, *sys.argv[1:]])
    finally:
        with transaction() as state:
            state["active"].pop(pid, None)
            state["queue"].pop(pid, None)


if __name__ == "__main__":
    raise SystemExit(main())
