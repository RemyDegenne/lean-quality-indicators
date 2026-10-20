"""Compare complete judge runs on the original first N samples of each library."""

import argparse
import itertools
import json
import tomllib
from pathlib import Path

from agreement import kappa, hyp_keys
from report import wilson

ROOT = Path(__file__).resolve().parent.parent


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--run", default="main")
    parser.add_argument("--limit", type=int, default=300)
    parser.add_argument("--labels", nargs="+", required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    run = ROOT / "runs" / args.run
    samples = [json.loads(line) for line in (run / "samples.jsonl").read_text().splitlines()]
    selected = [s for s in samples if int(s["id"].rsplit("-", 1)[1]) < args.limit]
    libraries = {lib["id"]: lib["name"] for lib in
                 tomllib.loads((ROOT / "libraries.toml").read_text())["library"]}
    results = {}
    for label in args.labels:
        base = run / "unnecessary-hypotheses" / label / "results"
        results[label] = {s["id"]: json.loads((base / f"{s['id']}.json").read_text())
                          for s in selected if (base / f"{s['id']}.json").exists()}
        if len(results[label]) != len(selected):
            raise SystemExit(f"{label}: incomplete ({len(results[label])}/{len(selected)}); no comparison written")

    def flagged(r):
        return r["verdict"] == "unnecessary_hypothesis_found"

    lines = ["# Unnecessary hypotheses: comparison of judges", "",
             f"Same first {args.limit} sampled theorems per library. Flags are judge claims.", "",
             "| Library | " + " | ".join(args.labels) + " |",
             "|---|" + "---:|" * len(args.labels)]
    for lib, name in libraries.items():
        ids = [s["id"] for s in selected if s["lib"] == lib]
        cells = []
        for label in args.labels:
            k = sum(flagged(results[label][i]) for i in ids)
            lo, hi = wilson(k, len(ids))
            cells.append(f"{k}/{len(ids)}: {k/len(ids):.1%} ({lo:.1%}–{hi:.1%})")
        lines.append(f"| {name} | " + " | ".join(cells) + " |")
    lines += ["", "## Pairwise agreement", "",
              "| First | Second | Library | Both | Either | Disagreements | Same hypothesis among both | κ |",
              "|---|---|---|---:|---:|---:|---:|---:|"]
    for first, second in itertools.combinations(args.labels, 2):
        for lib, name in [*libraries.items(), (None, "All")]:
            ids = [s["id"] for s in selected if lib is None or s["lib"] == lib]
            pairs = [(flagged(results[first][i]), flagged(results[second][i])) for i in ids]
            both = sum(a and b for a, b in pairs)
            either = sum(a or b for a, b in pairs)
            same = sum(bool(hyp_keys(results[first][i]) & hyp_keys(results[second][i]))
                       for i, (a, b) in zip(ids, pairs) if a and b)
            lines.append(f"| {first} | {second} | {name} | {both} | {either} | "
                         f"{sum(a != b for a, b in pairs)} | {same}/{both} | {kappa(pairs):.3f} |")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text("\n".join(lines) + "\n")
    print(f"Wrote {args.output}")


if __name__ == "__main__":
    main()
