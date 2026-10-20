#!/usr/bin/env python3
"""Codex executable wrapper: one shared session at a time, cooldown on HTTP 429.

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
    return bool(re.search(r"429\s+Too Many Requests|status(?:\s+code)?[\s:\"=]+429|"
                          r"rate_limit_exceeded", line, re.IGNORECASE))


def main():
    cmd = [os.environ.get("CODEX_REAL_BIN", "codex"), *sys.argv[1:]]
    if "--version" in sys.argv or "--help" in sys.argv:
        return subprocess.call(cmd)
    BASE.mkdir(parents=True, exist_ok=True)
    with (BASE / "codex-rate-guard-lock.log").open("a") as lock:
        # The lock covers both models and the entire judgment, including tool turns.
        fcntl.flock(lock, fcntl.LOCK_EX)
        try:
            state = json.loads(STATE.read_text())
        except (OSError, ValueError):
            state = {}
        delay = max(state.get("not_before", 0) - time.time(), 0)
        if delay:
            print(f"Rate guard: waiting {delay:.0f}s before another Codex session", file=sys.stderr, flush=True)
            time.sleep(delay)
        throttled = threading.Event()
        with subprocess.Popen(cmd, stdin=sys.stdin, stdout=subprocess.PIPE,
                              stderr=subprocess.PIPE, text=True, bufsize=1) as proc:
            def relay(source, target, stream):
                for line in source:
                    target.write(line)
                    target.flush()
                    if rate_error(line, stream) and not throttled.is_set():
                        throttled.set()
                        STATE.write_text(json.dumps({"not_before": time.time() + COOLDOWN}) + "\n")
                        with EVENTS.open("a") as events:
                            events.write(json.dumps({"time": time.time(), "event": "429",
                                                     "cooldown_seconds": COOLDOWN}) + "\n")
                        print("Rate guard: HTTP 429; aborting this attempt and cooling down for 300s",
                              file=sys.stderr, flush=True)
                        proc.terminate()
            threads = [threading.Thread(target=relay, args=(proc.stdout, sys.stdout, "stdout")),
                       threading.Thread(target=relay, args=(proc.stderr, sys.stderr, "stderr"))]
            for thread in threads:
                thread.start()
            while proc.poll() is None:
                if throttled.wait(1):
                    try:
                        proc.wait(timeout=5)
                    except subprocess.TimeoutExpired:
                        proc.kill()
                    break
            for thread in threads:
                thread.join(timeout=10)
            code = proc.wait()
        if not throttled.is_set():
            STATE.write_text(json.dumps({"not_before": time.time() + SPACING}) + "\n")
        return 75 if throttled.is_set() else code


if __name__ == "__main__":
    raise SystemExit(main())
