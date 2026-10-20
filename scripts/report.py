"""Summarise a judged run.

    python3 scripts/report.py --run pilot [--indicator unnecessary-hypotheses] [--label L]

Writes runs/<run>/<indicator>/<label>/report.md: per library, the number of samples judged,
the number flagged, the flag rate with a 95% Wilson interval, and every flagged theorem with
its source link and the judge's justification, for manual audit.
"""

from __future__ import annotations

import argparse
import json
import math
import sys
import tomllib
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import indicator  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent
META = {"id", "lib", "verdict", "model", "effort", "cost_usd", "duration_ms", "turns",
        "attempts", "judged"}


def wilson(k: int, n: int, z: float = 1.96) -> tuple[float, float]:
    if n == 0:
        return 0.0, 1.0
    p = k / n
    d = 1 + z * z / n
    c = (p + z * z / (2 * n)) / d
    h = z * math.sqrt(p * (1 - p) / n + z * z / (4 * n * n)) / d
    return max(0.0, c - h), min(1.0, c + h)


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--run", required=True)
    ap.add_argument("--indicator", default="unnecessary-hypotheses")
    ap.add_argument("--label", help="results subdirectory (default: the only one present)")
    args = ap.parse_args()
    run = ROOT / "runs" / args.run
    base = run / args.indicator
    if args.label:
        lab = base / args.label
    else:
        labels = sorted(p for p in base.iterdir() if p.is_dir())
        if len(labels) != 1:
            raise SystemExit(f"pick one of --label {[p.name for p in labels]}")
        lab = labels[0]
    names = {lib["id"]: lib["name"] for lib in
             tomllib.loads((ROOT / "libraries.toml").read_text())["library"]}
    cfg = indicator.config(ROOT / "indicators" / args.indicator)
    samples = [s for s in map(json.loads, (run / "samples.jsonl").open())
               if s["lib"] not in cfg["skip_libraries"]]
    results = {}
    for p in (lab / "results").glob("*.json"):
        if not p.name.endswith((".raw.json", ".transcript.jsonl")):
            r = json.loads(p.read_text())
            results[r["id"]] = r

    positive = cfg["positive"]
    split = positive if len(positive) > 1 else []  # one column per kind of finding
    field = cfg["split_field"]  # optional boolean field counted among the findings
    libs = list(dict.fromkeys(s["lib"] for s in samples))
    lines = [f"# {args.indicator}: run `{args.run}`, judge `{lab.name}`", "",
             "| Library | Sampled | Judged | Flagged | "
             + "".join(f"`{v}` | " for v in split)
             + (f"`{field}` | " if field else "") + "Rate | 95% CI | Cost |",
             "|---|---:|---:|---:|" + "---:|" * (len(split) + bool(field)) + "---:|---:|---:|"]
    table = []
    for lib in libs:
        ss = [s for s in samples if s["lib"] == lib]
        rs = [results[s["id"]] for s in ss if s["id"] in results]
        k = sum(r["verdict"] in positive for r in rs)
        n = len(rs)
        lo, hi = wilson(k, n)
        cost = sum(r.get("cost_usd") or 0 for r in rs)
        rate = f"{k / n:.1%}" if n else "–"
        kinds = "".join(f"{sum(r['verdict'] == v for r in rs)} | " for v in split)
        if field:
            kinds += f"{sum(r['verdict'] in positive and bool(r.get(field)) for r in rs)} | "
        row = (f"| {names.get(lib, lib)} | {len(ss)} | {n} | {k} | {kinds}{rate} | "
               f"{lo:.1%}–{hi:.1%} | ${cost:.2f} |")
        lines.append(row)
        table.append(row)
    lines.append("")
    lines.append("A flag is the judge's claim, not a verified fact: audit the list below. "
                 "`none_found` means the judge found nothing it could justify.")
    for lib in libs:
        flagged = [(s, results[s["id"]]) for s in samples
                   if s["lib"] == lib and s["id"] in results
                   and results[s["id"]]["verdict"] in positive]
        lines += ["", f"## {names.get(lib, lib)} ({len(flagged)} flagged)", ""]
        for s, r in flagged:
            lines.append(f"### [`{s['name']}`]({s['url']}) — `{s['id']}`")
            lines.append("")
            lines.append(f"Snippet: `{s['file']}`")
            lines.append("")
            if "hypotheses" in r:
                for h in r["hypotheses"]:
                    lines.append(f"- `{h['binder']}` ({h['source']}): {h['justification']}")
            else:
                lines.append(f"- **verdict**: `{r['verdict']}`")
                for k, v in r.items():
                    if k not in META and v:
                        lines.append(f"- **{k}**: {v}")
            lines.append("")
    (lab / "report.md").write_text("\n".join(lines) + "\n")
    print("\n".join(lines[2:4] + table))
    print(f"\nwrote {lab / 'report.md'}")


if __name__ == "__main__":
    main()
