"""Second, adversarial pass over the flags of a judged run.

    python3 scripts/verify.py --run main [--of claude-opus-5-5-high] [--jobs 8] \
        [--model claude-opus-5-5] [--effort high] [--claude PATH] [--report-only]

Every theorem the judge flagged goes, with the judge's claims, to a fresh session of the
`<indicator>-verify` judge (same tools and directories as the first judge), which tries to
refute each claim and answers `confirmed`, `refuted` or `uncertain` per claim. A flag
survives when at least one of its claims is confirmed.

Results: runs/<run>/<indicator>/<of>/verify/<model>-<effort>/results/<id>.json, and
verify-report.md next to them: per library the share of flags that survive (precision), the
rate of surviving flags among all judged theorems, and every claim with both verdicts.
"""

from __future__ import annotations

import argparse
import json
import os
import sys
import tomllib
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import judge  # noqa: E402
from report import wilson  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent
FOUND = "unnecessary_hypothesis_found"


def claims_text(res: dict) -> str:
    return "\n\n".join(f"{k}. `{h['binder']}` (from the {h['source']}): {h['justification']}"
                       for k, h in enumerate(res["hypotheses"], 1))


def outcome(ver: dict) -> str:
    vs = [c["verdict"] for c in ver["claims"]]
    if "confirmed" in vs:
        return "confirmed"
    return "refuted" if vs and all(v == "refuted" for v in vs) else "uncertain"


def report(run: Path, base: Path, out: Path, first: dict, ver: dict) -> None:
    names = {lib["id"]: lib["name"] for lib in
             tomllib.loads((ROOT / "libraries.toml").read_text())["library"]}
    samples = [json.loads(line) for line in (run / "samples.jsonl").open()]
    by_id = {s["id"]: s for s in samples}
    libs = list(dict.fromkeys(s["lib"] for s in samples))
    lines = [f"# Verification of `{base.name}` flags, run `{run.name}`, verifier "
             f"`{out.parent.name}`", "",
             "A flag survives when the verifier confirms at least one of its claims.", "",
             "| Library | Judged | Flags | Verified | Survive | Refuted | Uncertain | "
             "Precision (95% CI) | Surviving rate (95% CI) |",
             "|---|---:|---:|---:|---:|---:|---:|---:|---:|"]
    for lib in libs:
        judged = [i for i in first if by_id[i]["lib"] == lib]
        flags = [i for i in judged if first[i]["verdict"] == FOUND]
        done = [i for i in flags if i in ver]
        oc = [outcome(ver[i]) for i in done]
        k = oc.count("confirmed")
        plo, phi = wilson(k, len(done))
        # Unverified flags are left out of the surviving count, so this is a lower bound
        # until every flag has been verified.
        rlo, rhi = wilson(k, len(judged))
        prec = f"{k / len(done):.0%} ({plo:.0%}–{phi:.0%})" if done else "–"
        rate = f"{k / len(judged):.1%} ({rlo:.1%}–{rhi:.1%})" if judged else "–"
        lines.append(f"| {names.get(lib, lib)} | {len(judged)} | {len(flags)} | {len(done)} | "
                     f"{k} | {oc.count('refuted')} | {oc.count('uncertain')} | {prec} | {rate} |")
    for lib in libs:
        flagged = [s for s in samples if s["lib"] == lib and s["id"] in ver]
        lines += ["", f"## {names.get(lib, lib)}", ""]
        for s in flagged:
            v = ver[s["id"]]
            lines += [f"### [`{s['name']}`]({s['url']}) — `{s['id']}`: {outcome(v)}", ""]
            for h, c in zip(first[s["id"]]["hypotheses"], v["claims"]):
                lines.append(f"- `{h['binder']}` — **{c['verdict']}**")
                lines.append(f"  - judge: {h['justification']}")
                lines.append(f"  - verifier: {c['reason']}")
            if len(v["claims"]) != len(first[s["id"]]["hypotheses"]):
                lines.append(f"- (verifier answered {len(v['claims'])} claims for "
                             f"{len(first[s['id']]['hypotheses'])})")
            lines.append("")
    (out.parent / "verify-report.md").write_text("\n".join(lines) + "\n")
    print("\n".join(lines[4:6 + len(libs)]))
    print(f"\nwrote {out.parent / 'verify-report.md'}")


def load(d: Path) -> dict:
    return {p.stem: json.loads(p.read_text()) for p in d.glob("*.json")
            if not p.name.endswith(".raw.json")}


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--run", required=True)
    ap.add_argument("--indicator", default="unnecessary-hypotheses")
    ap.add_argument("--of", default="claude-opus-5-5-high", help="judge label to verify")
    ap.add_argument("--model", default="claude-opus-5-5")
    ap.add_argument("--effort", default="high", choices=["low", "medium", "high", "xhigh", "max"])
    ap.add_argument("--jobs", type=int, default=4)
    ap.add_argument("--retries", type=int, default=2)
    ap.add_argument("--timeout", type=int, default=1800)
    ap.add_argument("--max-budget", type=float, default=5.0)
    ap.add_argument("--claude", default=os.environ.get("CLAUDE_BIN", "claude"))
    ap.add_argument("--report-only", action="store_true")
    ap.add_argument("--ids", help="comma-separated sample ids (default: every flag)")
    args = ap.parse_args()

    run = ROOT / "runs" / args.run
    base = run / args.indicator / args.of
    ind = ROOT / "indicators" / f"{args.indicator}-verify"
    out = base / "verify" / f"{args.model}-{args.effort}" / "results"
    out.mkdir(parents=True, exist_ok=True)
    first = load(base / "results")
    samples = {json.loads(line)["id"]: json.loads(line) for line in (run / "samples.jsonl").open()}
    flagged = [i for i in samples if i in first and first[i]["verdict"] == FOUND]
    if args.ids:
        flagged = [i for i in flagged if i in args.ids.split(",")]
    todo = [] if args.report_only else [i for i in flagged if not (out / f"{i}.json").exists()]
    print(f"{len(flagged)} flags, {len(flagged) - len(todo)} already verified, {len(todo)} to go")
    cost = 0.0
    with ThreadPoolExecutor(args.jobs) as ex:
        futs = {ex.submit(judge.judge_one, samples[i], run, ind, out, args,
                          {"{claims}": claims_text(first[i])}): i for i in todo}
        for n, f in enumerate(as_completed(futs), 1):
            i = futs[f]
            try:
                r = f.result()
                cost += r.get("cost_usd") or 0
                print(f"[{n}/{len(todo)}] {i:24} {outcome(r):9} ${cost:.2f} total", flush=True)
            except Exception as e:  # noqa: BLE001
                (out.parent / "errors.log").open("a").write(f"{i}\t{e}\n")
                print(f"[{n}/{len(todo)}] {i:24} ERROR {e}", flush=True)
    report(run, base, out, first, load(out))


if __name__ == "__main__":
    main()
