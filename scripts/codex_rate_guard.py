#!/usr/bin/env python3
"""Codex executable wrapper: adjustable shared concurrency, live backoff on HTTP 429.

Use CODEX_BIN=/absolute/path/to/this/script with judge.py or benchmark.py.
CODEX_REAL_BIN selects the real CLI (default codex). This changes request scheduling
only; the model, prompt, tools and verdict schema are passed through unchanged.
"""

import fcntl
import json
import os
import re
import subprocess
import sys
import threading
import contextlib
import time
from pathlib import Path

BASE = Path(__file__).resolve().parent.parent / "runs/main/unnecessary-hypotheses"
STATE = BASE / "codex-rate-guard-state.log"
EVENTS = BASE / "codex-rate-guard-events.log"
COOLDOWN = 300
SPACING = 10


def rate_error(line: str, stream: str) -> bool:
    if stream == "stdout":
        try:
            event = json.loads(line)
        except ValueError:
            return False
        item = event.get("item", {})
        if event.get("type") not in {"error", "turn.failed"} and item.get("type") != "error":
            return False
    return bool(re.search(r"\b429\b|too many requests|rate_limit_exceeded", line, re.IGNORECASE))


def alive(pid: str) -> bool:
    try:
        os.kill(int(pid), 0)
        status = Path(f"/proc/{pid}/stat")
        return not status.exists() or status.read_text().split(") ", 1)[1][0] != "Z"
    except (ProcessLookupError, ValueError, FileNotFoundError):
        return False


def event(kind: str, **details):
    # Called while holding the shared state lock.
    with EVENTS.open("a") as output:
        output.write(json.dumps({"time": time.time(), "event": kind, **details}) + "\n")


@contextlib.contextmanager
def transaction():
    BASE.mkdir(parents=True, exist_ok=True)
    with (BASE / "codex-rate-guard-lock.log").open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        try:
            state = json.loads(STATE.read_text())
        except (OSError, ValueError):
            state = {}
        for key, default in {"limit": 1, "spacing": SPACING, "not_before": 0,
                             "next_start": 0, "epoch": 0, "active": {}, "queue": {}}.items():
            state.setdefault(key, default)
        for kind in ["active", "queue"]:
            state[kind] = {pid: value for pid, value in state[kind].items() if alive(pid)}
        yield state
        temporary = BASE / "codex-rate-guard-pending.log"
        temporary.write_text(json.dumps(state) + "\n")
        temporary.replace(STATE)


def configure(limit: int, spacing: float, reason: str):
    if not 1 <= limit <= 16 or not 0 <= spacing <= 60:
        raise ValueError("Limit must be 1..16 and spacing 0..60 seconds")
    with transaction() as state:
        state.update(limit=limit, spacing=spacing, last_change=time.time())
        event("configuration", limit=limit, spacing=spacing, reason=reason)


def snapshot() -> dict:
    with transaction() as state:
        return json.loads(json.dumps(state))


def admit(pid: str, model: str):
    with transaction() as state:
        state["queue"].setdefault(pid, {"model": model, "queued": time.time()})
        now = time.time()
        if now < max(state["not_before"], state["next_start"]) or len(state["active"]) >= state["limit"]:
            return None
        queue = sorted(state["queue"], key=lambda p: state["queue"][p]["queued"])
        # Alternate models when both have work waiting, rather than allowing a
        # whole pool of one model to occupy every slot first.
        other = [p for p in queue if state["queue"][p]["model"] != state.get("last_model")]
        if (other or queue)[0] != pid:
            return None
        state["queue"].pop(pid)
        state["active"][pid] = {"model": model, "started": now}
        state["next_start"] = now + state["spacing"]
        state["last_model"] = model
        event("session_started", pid=pid, model=model, limit=state["limit"],
              active=len(state["active"]), spacing=state["spacing"])
        return state["epoch"], now


def backoff(model: str):
    with transaction() as state:
        now = time.time()
        before = state["limit"]
        if state["not_before"] <= now:
            state["limit"] = max(1, before // 2)
            state["epoch"] += 1
        state["not_before"] = max(state["not_before"], now + COOLDOWN)
        state["last_429"] = now
        state["last_change"] = now
        event("rate_limit", model=model, previous_limit=before, limit=state["limit"],
              cooldown_seconds=COOLDOWN)


def finish(pid: str, model: str, started: float, code: int):
    with transaction() as state:
        state["active"].pop(pid, None)
        state["queue"].pop(pid, None)
        event("session_finished", pid=pid, model=model, code=code,
              duration_seconds=time.time() - started)


def main():
    cmd = [os.environ.get("CODEX_REAL_BIN", "codex"), *sys.argv[1:]]
    if "--version" in sys.argv or "--help" in sys.argv:
        return subprocess.call(cmd)
    model = sys.argv[sys.argv.index("--model") + 1] if "--model" in sys.argv else "unknown"
    pid = str(os.getpid())
    admission = None
    while admission is None:
        admission = admit(pid, model)
        if admission is None:
            time.sleep(1)
    epoch, started = admission
    throttled = threading.Event()
    code = 1
    try:
        with subprocess.Popen(cmd, stdin=sys.stdin, stdout=subprocess.PIPE,
                              stderr=subprocess.PIPE, text=True, bufsize=1) as proc:
            def relay(source, target, stream):
                for line in source:
                    target.write(line)
                    target.flush()
                    if rate_error(line, stream) and not throttled.is_set():
                        throttled.set()
                        backoff(model)
                        print("Rate guard: HTTP 429; reducing concurrency and cooling down for 300s",
                              file=sys.stderr, flush=True)
                        proc.terminate()
            threads = [threading.Thread(target=relay, args=(proc.stdout, sys.stdout, "stdout")),
                       threading.Thread(target=relay, args=(proc.stderr, sys.stderr, "stderr"))]
            for thread in threads:
                thread.start()
            while proc.poll() is None:
                if snapshot()["epoch"] != epoch:
                    throttled.set()
                if throttled.wait(1):
                    proc.terminate()
                    try:
                        proc.wait(timeout=5)
                    except subprocess.TimeoutExpired:
                        proc.kill()
                    break
            for thread in threads:
                thread.join(timeout=10)
            code = 75 if throttled.is_set() else proc.wait()
        return code
    finally:
        finish(pid, model, started, code)


if __name__ == "__main__":
    raise SystemExit(main())
