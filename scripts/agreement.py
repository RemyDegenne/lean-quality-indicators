"""Compare two judge passes on the same theorems (test-retest).

    python3 scripts/agreement.py --run main [--ids-file runs/main/rejudge-ids.json] \
        [--first claude-opus-5-5-high] [--second rejudge-claude-opus-5-5-high]

The ids file maps each library to {"flagged": [...], "controls": [...]}: the theorems the
first pass flagged and as many it did not flag. For each library: how many first-pass flags
the second pass flags again, how many controls it flags, whether repeated flags name the same
hypothesis, and Cohen's kappa on this (enriched) set. Writes agreement.md next to the second
pass's results, with every disagreement.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
import tomllib
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from report import wilson  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent
FOUND = "unnecessary_hypothesis_found"


def hyp_keys(r: dict) -> set[str]:
    """Names of the flagged hypotheses: the binder's variable name, or its class."""
    keys = set()
    for h in r.get("hypotheses", []):
        b = h["binder"]
        m = re.match(r"\s*[\(\{⦃\[]\s*([^:\]\)\}]+?)\s*:", b)
        keys.add((m.group(1) if m else re.sub(r"\s+", "", b)).strip())
    return keys


def kappa(pairs: list[tuple[bool, bool]]) -> float:
    n = len(pairs)
    if not n:
        return float("nan")
    po = sum(a == b for a, b in pairs) / n
    pa = sum(a for a, _ in pairs) / n
    pb = sum(b for _, b in pairs) / n
    pe = pa * pb + (1 - pa) * (1 - pb)
    return (po - pe) / (1 - pe) if pe < 1 else 1.0


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--run", required=True)
    ap.add_argument("--ids-file", help="flagged/controls selection (default: whole sample)")
    ap.add_argument("--indicator", default="unnecessary-hypotheses")
    ap.add_argument("--first", default="claude-opus-5-5-high")
    ap.add_argument("--second", default="rejudge-claude-opus-5-5-high")
    args = ap.parse_args()
    run = ROOT / "runs" / args.run
    base = run / args.indicator
    names = {lib["id"]: lib["name"] for lib in
             tomllib.loads((ROOT / "libraries.toml").read_text())["library"]}
    samples = {json.loads(line)["id"]: json.loads(line) for line in (run / "samples.jsonl").open()}

    def load(label: str, i: str) -> dict | None:
        p = base / label / "results" / f"{i}.json"
        return json.loads(p.read_text()) if p.exists() else None

    if args.ids_file:
        sel = json.loads((ROOT / args.ids_file).read_text())
        others = "Controls flagged"
    else:  # the whole sample: first-pass flags against everything else
        sel = {}
        for i, s in samples.items():
            a = load(args.first, i)
            if a:
                grp = "flagged" if a["verdict"] == FOUND else "controls"
                sel.setdefault(s["lib"], {"flagged": [], "controls": []})[grp].append(i)
        others = "Non-flags flagged"

    lines = [f"# Test-retest: `{args.first}` vs `{args.second}`, run `{args.run}`", "",
             "The second pass judged each theorem in a fresh session, without the first verdict.",
             "", f"| Library | Flags re-flagged | {others} | Same hypothesis | κ |",
             "|---|---:|---:|---:|---:|"]
    detail = []
    allpairs = []
    for lib, groups in sel.items():
        pairs, same, both = [], 0, 0
        cells = {}
        for grp in ("flagged", "controls"):
            judged = [(i, load(args.first, i), load(args.second, i)) for i in groups[grp]]
            judged = [(i, a, b) for i, a, b in judged if a and b]
            k = sum(b["verdict"] == FOUND for _, _, b in judged)
            lo, hi = wilson(k, len(judged))
            cells[grp] = f"{k}/{len(judged)} ({lo:.0%}–{hi:.0%})" if judged else "–"
            for i, a, b in judged:
                fa, fb = a["verdict"] == FOUND, b["verdict"] == FOUND
                pairs.append((fa, fb))
                if fa and fb:
                    both += 1
                    same += bool(hyp_keys(a) & hyp_keys(b))
                if fa != fb:
                    detail.append((lib, i, a, b))
        allpairs += pairs
        lines.append(f"| {names.get(lib, lib)} | {cells['flagged']} | {cells['controls']} | "
                     f"{same}/{both} | {kappa(pairs):.2f} |")
    note = ("on an enriched sample, half flags, so it is not the κ of a random sample"
            if args.ids_file else f"on the {len(allpairs)} theorems judged by both passes")
    lines += ["", f"Overall κ: {kappa(allpairs):.2f} ({note}).", ""]
    for lib in sel:
        rows = [d for d in detail if d[0] == lib]
        lines += [f"## {names.get(lib, lib)}: {len(rows)} disagreements", ""]
        for _, i, a, b in rows:
            s = samples[i]
            who = "flagged first, not again" if a["verdict"] == FOUND else "flagged only second"
            lines += [f"### [`{s['name']}`]({s['url']}) — `{i}`: {who}", ""]
            for h in (a if a["verdict"] == FOUND else b)["hypotheses"]:
                lines.append(f"- `{h['binder']}`: {h['justification']}")
            lines.append("")
    out = base / args.second / ("agreement.md" if args.ids_file else "agreement-full.md")
    out.write_text("\n".join(lines) + "\n")
    print("\n".join(lines[4:6 + len(sel) + 2]))
    print(f"wrote {out}")


if __name__ == "__main__":
    main()
