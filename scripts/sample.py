"""Draw a random sample of theorems from each library and extract their context.

    python3 scripts/sample.py --run pilot --n 50 [--seed 0] [--libs mathlib,tauceti]
    python3 scripts/sample.py --population-only [--diagnose]

The population of a library is every `theorem`/`lemma` in the included files of its pinned
sources (libraries.toml, libraries.lock.json), minus excluded paths and deprecated
declarations. It is cached in data/population/<lib>.jsonl, keyed by the pinned commits.

Each sampled theorem is written to runs/<run>/samples/<lib>/<id>.lean: the enclosing
`namespace`/`section` openers and the `variable`, `open`, `universe`, `include`, `omit`,
`set_option`, local attribute/instance and notation commands in effect, then the theorem
with its proof, with doc comments removed. runs/<run>/samples.jsonl records where each one
came from (pinned commit, path, lines, GitHub link).
"""

from __future__ import annotations

import argparse
import collections
import datetime
import fnmatch
import hashlib
import json
import os
import random
import re
import sys
import tomllib
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import leanscan  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent
REPOS = ROOT / "repos"
POP = ROOT / "data" / "population"


def load_config():
    cfg = tomllib.loads((ROOT / "libraries.toml").read_text())
    lock = json.loads((ROOT / "libraries.lock.json").read_text())
    return cfg, lock


def source_files(defaults: dict, src: dict) -> list[str]:
    base = REPOS / src["dir"]
    excl = defaults.get("exclude", []) + src.get("exclude", [])
    out = []
    for inc in src["include"]:
        for dirpath, dirnames, filenames in os.walk(base / inc):
            dirnames[:] = sorted(d for d in dirnames if d != ".lake")
            for fn in sorted(filenames):
                if not fn.endswith(".lean"):
                    continue
                rel = os.path.relpath(os.path.join(dirpath, fn), base)
                if not any(fnmatch.fnmatch(rel, p) for p in excl):
                    out.append(rel)
    return out


def _scan_file(job):
    src_dir, rel, ctx_cmds, other_cmds = job
    text = (REPOS / src_dir / rel).read_text(encoding="utf-8", errors="replace")
    ths, _ = leanscan.scan(text, set(ctx_cmds), set(other_cmds), with_context=False)
    return src_dir, rel, [(t.cmd.line, t.end_line, t.name, t.full_name, t.cmd.head,
                           t.deprecated, "private" in t.cmd.mods) for t in ths]


def _unknown_starts(job):
    """Column-0 words (outside comments) that the scanner does not treat as commands."""
    src_dir, rel, ctx_cmds, other_cmds = job
    text = (REPOS / src_dir / rel).read_text(encoding="utf-8", errors="replace")
    masked, _ = leanscan.mask(text)
    extra = set(ctx_cmds) | set(other_cmds)
    c = collections.Counter()
    for line in masked.split("\n"):
        m = leanscan._WORD_RE.match(line)
        if m and not leanscan._is_start_word(m.group(), extra):
            c[m.group()] += 1
    return c


def population(cfg, lock, lib, workers: int, diagnose: bool = False):
    defaults = cfg.get("defaults", {})
    key = hashlib.sha256(json.dumps(
        [lib, defaults, [(s, lock[s["dir"]]["commit"]) for s in lib["source"]],
         Path(leanscan.__file__).read_text(), Path(__file__).read_text()],
        sort_keys=True).encode()).hexdigest()[:16]
    cache = POP / f"{lib['id']}.jsonl"
    meta = POP / f"{lib['id']}.meta.json"
    if not diagnose and cache.exists() and meta.exists() and \
            json.loads(meta.read_text())["key"] == key:
        return [json.loads(line) for line in cache.open()], json.loads(meta.read_text())
    jobs = []
    for src in lib["source"]:
        for rel in source_files(defaults, src):
            jobs.append((src["dir"], rel, src.get("context_commands", []),
                         src.get("other_commands", [])))
    print(f"[{lib['id']}] scanning {len(jobs)} files", file=sys.stderr)
    if diagnose:
        total = collections.Counter()
        with ProcessPoolExecutor(workers) as ex:
            for c in ex.map(_unknown_starts, jobs, chunksize=64):
                total.update(c)
        print(f"[{lib['id']}] unrecognised column-0 words: {total.most_common(25)}",
              file=sys.stderr)
    rows, n_dep, n_priv = [], 0, 0
    with ProcessPoolExecutor(workers) as ex:
        for src_dir, rel, ths in ex.map(_scan_file, jobs, chunksize=64):
            for line, end_line, name, full, head, dep, priv in ths:
                if dep and defaults.get("skip_deprecated", True):
                    n_dep += 1
                    continue
                if priv and defaults.get("skip_private", True):
                    n_priv += 1
                    continue
                rows.append({"lib": lib["id"], "dir": src_dir, "path": rel, "line": line,
                             "end_line": end_line, "name": full, "keyword": head})
    POP.mkdir(parents=True, exist_ok=True)
    with cache.open("w") as f:
        for r in rows:
            f.write(json.dumps(r, ensure_ascii=False) + "\n")
    info = {"key": key, "files": len(jobs), "theorems": len(rows),
            "skipped_deprecated": n_dep, "skipped_private": n_priv,
            "built": datetime.datetime.now().isoformat(timespec="seconds")}
    meta.write_text(json.dumps(info, indent=1) + "\n")
    return rows, info


def extract(lock, src_cfg, row) -> str:
    text = (REPOS / row["dir"] / row["path"]).read_text(encoding="utf-8", errors="replace")
    ths, docs = leanscan.scan(text, set(src_cfg.get("context_commands", [])),
                              set(src_cfg.get("other_commands", [])))
    match = [t for t in ths if t.cmd.line == row["line"]]
    if len(match) != 1:
        raise RuntimeError(f"cannot relocate {row}")
    return leanscan.render_context(text, docs, match[0])


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--run", help="run name (directory under runs/)")
    ap.add_argument("--n", type=int, help="theorems per library")
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--libs", help="comma-separated library ids (default: all)")
    ap.add_argument("--workers", type=int, default=os.cpu_count())
    ap.add_argument("--extend", action="store_true",
                    help="add --n more theorems per library to an existing run (same seed)")
    ap.add_argument("--population-only", action="store_true")
    ap.add_argument("--diagnose", action="store_true",
                    help="also report column-0 words the scanner does not recognise")
    args = ap.parse_args()
    cfg, lock = load_config()
    libs = cfg["library"]
    if args.libs:
        want = args.libs.split(",")
        libs = [lib for lib in libs if lib["id"] in want]
    pops = {}
    for lib in libs:
        rows, info = population(cfg, lock, lib, args.workers, args.diagnose)
        pops[lib["id"]] = (rows, info)
        print(f"{lib['id']:16} {info['files']:7} files {info['theorems']:8} theorems "
              f"({info['skipped_deprecated']} deprecated, "
              f"{info.get('skipped_private', 0)} private skipped)")
    if args.population_only:
        return
    if not (args.run and args.n):
        ap.error("--run and --n are required to draw a sample")
    run = ROOT / "runs" / args.run
    old: list[dict] = []
    if (run / "samples.jsonl").exists():
        if not args.extend:
            sys.exit(f"{run} already has samples; pick another run name or pass --extend")
        old = [json.loads(line) for line in (run / "samples.jsonl").open()]
        args.seed = json.loads((run / "run.json").read_text())["seed"]
    out = list(old)
    src_by_dir = {s["dir"]: s for lib in libs for s in lib["source"]}
    for lib in libs:
        rows, _ = pops[lib["id"]]
        prev = [s for s in old if s["lib"] == lib["id"]]
        rng = random.Random(f"{args.seed}:{lib['id']}")
        picked = rng.sample(range(len(rows)), min(len(prev) + args.n, len(rows)))
        (run / "samples" / lib["id"]).mkdir(parents=True, exist_ok=True)
        for k, i in enumerate(picked):
            row = rows[i]
            if k < len(prev):
                # The first draws reproduce the existing sample, so the union stays uniform.
                if (prev[k]["dir"], prev[k]["path"], prev[k]["line"]) != \
                        (row["dir"], row["path"], row["line"]):
                    sys.exit(f"cannot extend: the population of {lib['id']} has changed")
                continue
            sid = f"{lib['id']}-{k:04d}"
            snippet = extract(lock, src_by_dir[row["dir"]], row)
            rel_file = f"samples/{lib['id']}/{sid}.lean"
            (run / rel_file).write_text(snippet)
            commit = lock[row["dir"]]["commit"]
            url = f"{lock[row['dir']]['url']}/blob/{commit}/{row['path']}" \
                  f"#L{row['line']}-L{row['end_line']}"
            out.append({"id": sid, **row, "commit": commit, "url": url, "file": rel_file,
                        "snippet_lines": snippet.count("\n"), "snippet_chars": len(snippet)})
    with (run / "samples.jsonl").open("w") as f:
        for r in out:
            f.write(json.dumps(r, ensure_ascii=False) + "\n")
    now = datetime.datetime.now().isoformat(timespec="seconds")
    meta = json.loads((run / "run.json").read_text()) if old else {
        "created": now, "seed": args.seed, "n": 0,
        "population": {k: v[1] for k, v in pops.items()},
        "commits": {d: v["commit"] for d, v in lock.items()}, "draws": []}
    meta["n"] += args.n
    meta.setdefault("draws", []).append({"date": now, "n": args.n})
    (run / "run.json").write_text(json.dumps(meta, indent=1) + "\n")
    print(f"wrote {len(out) - len(old)} new samples to {run} ({len(out)} in total)")


if __name__ == "__main__":
    main()
