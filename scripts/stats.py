"""Progress of a judge run.

    python3 scripts/stats.py --run main [--indicator unnecessary-hypotheses] [--label L]

Per library: sampled, judged, flagged (with rate), failed calls; then overall progress,
cost, throughput over the last 10 minutes and estimated time to completion.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import indicator  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--run", required=True)
    ap.add_argument("--indicator", default="unnecessary-hypotheses")
    ap.add_argument("--label", default="claude-opus-5-5-high")
    args = ap.parse_args()
    run = ROOT / "runs" / args.run
    lab = run / args.indicator / args.label
    cfg = indicator.config(ROOT / "indicators" / args.indicator)
    positive = cfg["positive"]
    samples = [s for s in map(json.loads, (run / "samples.jsonl").open())
               if s["lib"] not in cfg["skip_libraries"]]
    results, mtimes = {}, []
    for p in (lab / "results").glob("*.json"):
        if not p.name.endswith(".raw.json"):
            results[p.stem] = json.loads(p.read_text())
            mtimes.append(p.stat().st_mtime)
    failed = set()
    if (lab / "errors.log").exists():
        failed = {line.split("\t")[0] for line in (lab / "errors.log").open()} - set(results)

    print(f"{'library':16} {'sampled':>7} {'judged':>6} {'flagged':>7} {'rate':>6} {'failed':>6}")
    for lib in dict.fromkeys(s["lib"] for s in samples):
        ids = [s["id"] for s in samples if s["lib"] == lib]
        rs = [results[i] for i in ids if i in results]
        k = sum(r["verdict"] in positive for r in rs)
        rate = f"{k / len(rs):.1%}" if rs else "-"
        print(f"{lib:16} {len(ids):7} {len(rs):6} {k:7} {rate:>6} "
              f"{sum(i in failed for i in ids):6}")
    total, done = len(samples), sum(s["id"] in results for s in samples)
    cost = sum(r.get("cost_usd") or 0 for r in results.values())
    now = time.time()
    recent = sum(t > now - 600 for t in mtimes) / 10
    running = subprocess.run(["pgrep", "-f", f"judge.py --run {args.run}"],
                             capture_output=True).returncode == 0
    eta = f", ETA {(total - done) / recent:.0f} min" if recent and done < total else ""
    print(f"\n{done}/{total} judged, ${cost:.2f} at API rates, "
          f"{recent:.1f}/min over the last 10 min{eta}; judge "
          f"{'running' if running else 'NOT running'}")


if __name__ == "__main__":
    main()
