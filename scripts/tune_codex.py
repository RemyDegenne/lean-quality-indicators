"""Conservatively tune shared Sol/Luna concurrency using live guard events.

    python3 -u scripts/tune_codex.py --minutes 45 --max-sessions 8

Raises the limit by one after five clean minutes and at least four completions.
A 429 immediately halves concurrency and triggers the guard's shared cooldown.
If a higher setting fails to improve throughput, retains the previous setting.
After tuning, leaves the fastest setting validated for at least five clean minutes;
the rate guard remains active for the remainder of the benchmark.
"""

import argparse
import collections
import datetime
import json
from pathlib import Path
import time

import codex_rate_guard as guard


def read_events():
    if not guard.EVENTS.exists():
        return []
    events = []
    for line in guard.EVENTS.read_text().splitlines():
        try:
            events.append(json.loads(line))
        except ValueError:
            pass  # The current final line can still be being written.
    return events


def window(events, since):
    rows = [e for e in events if e["time"] >= since]
    finished = [e for e in rows if e["event"] == "session_finished" and e["code"] == 0]
    return finished, sum(e["event"] == "rate_limit" for e in rows)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--minutes", type=float, default=45)
    parser.add_argument("--max-sessions", type=int, default=8)
    parser.add_argument("--stage-seconds", type=int, default=300)
    parser.add_argument("--spacing", type=float, default=5)
    parser.add_argument("--interval", type=int, default=30)
    parser.add_argument("--completion-marker", type=Path,
                        default=guard.BASE / "benchmark-complete.json",
                        help="stop when this benchmark's success marker exists")
    args = parser.parse_args()
    if args.minutes <= 0 or not 1 <= args.max_sessions <= 16 or args.stage_seconds < 60:
        parser.error("Positive duration, max sessions 1..16 and stage at least 60 seconds required")
    start = time.time()
    end = start + args.minutes * 60
    state = guard.snapshot()
    guard.configure(state["limit"], args.spacing, "Start supervised tuning")
    stage_start = max(start, state["not_before"])
    current = state["limit"]
    observed_errors = 0
    stable = {}
    blocked_above = None
    stage_log = guard.BASE / "codex-tuning-stages.log"
    # A higher setting must beat the preceding stable rate by at least 5%.
    previous_rate = None
    while time.time() < end:
        if args.completion_marker.exists():
            print("Benchmark complete; stopping tuner", flush=True)
            break
        now = time.time()
        events = read_events()
        finished, errors = window(events, start)
        state = guard.snapshot()
        if errors > observed_errors:
            blocked_above = current if blocked_above is None else min(blocked_above, current)
            observed_errors = errors
            current = state["limit"]
            stage_start = max(now, state["not_before"])
            previous_rate = None
            stable = {k: v for k, v in stable.items() if k < blocked_above}
        stage_finished, _ = window(events, stage_start)
        elapsed = max(0, now - stage_start)
        rate = len(stage_finished) * 60 / elapsed if elapsed else 0
        counts = collections.Counter(e["model"] for e in finished)
        status = {"utc": datetime.datetime.now(datetime.timezone.utc).isoformat(timespec="seconds"),
                  "elapsed_minutes": round((now-start)/60, 1), "limit": state["limit"],
                  "spacing_seconds": state["spacing"],
                  "active": len(state["active"]), "queued": len(state["queue"]),
                  "cooldown_seconds": round(max(0, state["not_before"] - now)),
                  "completed": dict(counts), "429s": errors,
                  "stage_minutes": round(elapsed/60, 1), "stage_per_minute": round(rate, 2)}
        print(json.dumps(status), flush=True)
        if elapsed >= args.stage_seconds and len(stage_finished) >= 4:
            stage = {"time": now, "limit": current, "minutes": elapsed/60,
                     "spacing_seconds": state["spacing"],
                     "completed": len(stage_finished), "per_minute": rate, "429s": 0}
            with stage_log.open("a") as output:
                output.write(json.dumps(stage) + "\n")
            stable[current] = stage
            if previous_rate is not None and rate < previous_rate * 1.05:
                best = max(stable, key=lambda k: stable[k]["per_minute"])
                guard.configure(best, args.spacing, "No throughput improvement from higher concurrency")
                current = best
                blocked_above = min(blocked_above or args.max_sessions + 1, best + 1)
            elif current < args.max_sessions and (blocked_above is None or current + 1 < blocked_above):
                previous_rate = rate
                current += 1
                guard.configure(current, args.spacing, "Five clean minutes; increase by one")
            stage_start = now
        time.sleep(min(args.interval, max(0, end - time.time())))
    if stable:
        best = max(stable, key=lambda k: stable[k]["per_minute"])
        # Do not override a more recent automatic backoff.
        final_state = guard.snapshot()
        if final_state.get("last_429", 0) < stable[best]["time"]:
            guard.configure(best, args.spacing, "Finish tuning at fastest validated clean setting")
    result = {"started": start, "finished": time.time(), "stable_stages": stable,
              "rate_errors": observed_errors, "final": guard.snapshot()}
    (guard.BASE / "codex-tuning-result.log").write_text(json.dumps(result, indent=2) + "\n")
    print("Tuning finished; guard remains active", flush=True)


if __name__ == "__main__":
    main()
