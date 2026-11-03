"""Explicit unfoldings of definitions (def_unfolds.py, source backend) on every corpus
library: the five libraries of libraries.toml, OpenAI Math and CFSG.

    python3 scripts/def_unfolds_corpus.py --fetch       # clone the packages the sources pin
    python3 scripts/def_unfolds_corpus.py               # measure every library
    python3 scripts/def_unfolds_corpus.py --only tauceti flt-anthropic
    python3 scripts/def_unfolds_corpus.py --table       # only rebuild the comparison table
    python3 scripts/def_unfolds_corpus.py --ilean --only mathlib tauceti   # built libraries

The sources themselves come from scripts/fetch.py (libraries.toml), the OpenAI Math clone
in repos/openai-math and scripts/fetch_cfsg.py. Each library is measured in the scope of
the other audits (`include`/`exclude`). Names are resolved against every package of the
source's lake-manifest.json and the Lean core sources of its toolchain, or of the nearest
installed toolchain. A library made of several repositories (Formal Frontier) is
measured repository by repository, then merged.

`--ilean` runs the ilean backend (Lean's own name resolution) on a library whose Lake
project is built (`.lake/build`), in the same scope, writes `ilean/<library>/` and compares
it with the source backend's output (`comparison.md`). Run the source backend with
`--save-uses` first to also match individual uses.
"""
from __future__ import annotations

import argparse
import json
import re
import shutil
import subprocess
import sys
import tomllib
from collections import Counter
from pathlib import Path

import def_unfolds as du
import fetch

ROOT = Path(__file__).resolve().parent.parent
REPOS = ROOT / "repos"
OUT = ROOT / "runs/def-unfolds-2026-11-02"
TOOLCHAINS = Path.home() / ".elan/toolchains"
def _source(defaults: dict, s: dict) -> dict:
    return {"dir": s["dir"], "include": s["include"],
            "exclude": defaults.get("exclude", []) + s.get("exclude", []),
            "commands": s.get("context_commands", []) + s.get("other_commands", [])}


def libraries() -> list[tuple[str, str, list[dict]]]:
    out = []
    for path in (ROOT / "libraries.toml", ROOT / "runs/openai-math-2026-10-21/libraries.toml"):
        cfg = tomllib.loads(path.read_text())
        for lib in cfg["library"]:
            out.append((lib["id"], lib["name"],
                        [_source(cfg.get("defaults", {}), s) for s in lib["source"]]))
    out.append(("axiom-cfsg", "CFSG (AxiomMath)",
                [{"dir": "axiom-cfsg", "include": ["CFSG/"], "exclude": ["*/Certificates/*"],
                  "commands": []}]))
    return out


def lake_root(src: dict) -> tuple[Path, list[str], list[str]]:
    """The Lake project of a source, and its include/exclude relative to it."""
    repo = REPOS / src["dir"]
    parts = src["include"][0].strip("/").split("/")
    root, prefix = repo, ""
    for i in range(1, len(parts)):
        d = repo.joinpath(*parts[:i])
        if (d / "lake-manifest.json").exists() or (d / "lean-toolchain").exists():
            root, prefix = d, "/".join(parts[:i]) + "/"
    strip = (lambda p: p[len(prefix):] if prefix and p.startswith(prefix) else p)
    return root, [strip(p) for p in src["include"]], [strip(p) for p in src["exclude"]]


def packages(root: Path) -> list[dict]:
    m = root / "lake-manifest.json"
    if not m.exists():
        return []
    return [p for p in json.loads(m.read_text())["packages"]
            if p.get("type", "git") == "git" and p.get("rev") and p.get("url")]


def _version(v: str):
    m = re.match(r"v(\d+)\.(\d+)\.(\d+)(?:-rc(\d+))?", v)
    if not m:
        return None
    major, minor, patch, rc = m.groups()
    return int(major), int(minor), int(patch), int(rc) if rc else 99


def core_dir(root: Path) -> tuple[Path, str]:
    """Lean core sources for the project's toolchain, or the nearest installed release."""
    tc = (root / "lean-toolchain").read_text().strip() if (root / "lean-toolchain").exists() \
        else ""
    exact = TOOLCHAINS / tc.replace("/", "--").replace(":", "---") / "src/lean"
    if tc and exact.is_dir():
        return exact, tc
    want = _version(tc.rsplit(":", 1)[-1]) or (99, 0, 0, 0)
    installed = sorted((v, d) for d in TOOLCHAINS.glob("leanprover--lean4---v*")
                       if (d / "src/lean").is_dir()
                       and (v := _version(d.name.rsplit("---", 1)[-1])))
    below = [x for x in installed if x[0] <= want]
    v, d = below[-1] if below else installed[0]
    return d / "src/lean", f"{tc} (Lean core of {d.name.rsplit('---', 1)[-1]} used)"


def do_fetch(only: set[str]):
    for lib_id, _, sources in libraries():
        if only and lib_id not in only:
            continue
        for src in sources:
            root, _, _ = lake_root(src)
            if not root.exists():
                print(f"missing source {root}: clone it first", file=sys.stderr)
                continue
            for p in packages(root):
                name = p["name"].strip("«»")
                try:
                    fetch.fetch_dep(name, p["url"], p["rev"])
                except subprocess.CalledProcessError as e:
                    shutil.rmtree(fetch.dep_dir(name, p["rev"]), ignore_errors=True)
                    print(f"failed: {name} {p['rev'][:12]} ({p['url']}): {e}", file=sys.stderr)


def _measure_source(lib_id: str, name: str, src: dict, jobs: int, uses=None):
    root, include, exclude = lake_root(src)
    deps = [fetch.dep_dir(p["name"].strip("«»"), p["rev"]) for p in packages(root)]
    missing = [str(d) for d in deps if not d.exists()]
    deps = [d for d in deps if d.exists()]
    core, toolchain = core_dir(root)
    print(f"== {lib_id}: {src['dir']}", file=sys.stderr)
    meta, rows, unf = du.run_source(root, include, exclude, deps + [core], jobs, name, uses,
                                    src["commands"])
    meta.update({"library": lib_id, "source": src["dir"], "toolchain": toolchain,
                 "missing_deps": [du.display_path(d) for d in missing]})
    return meta, rows, unf


def measure(lib_id: str, name: str, sources: list[dict], jobs: int, save_uses=False):
    out = OUT / lib_id
    if len(sources) == 1:
        uses = [] if save_uses else None
        meta, rows, unf = _measure_source(lib_id, name, sources[0], jobs, uses)
        du.write_output(out, meta, rows, unf, uses)
        return
    all_rows, all_unf, metas, diag = [], [], [], Counter()
    for src in sources:
        meta, rows, unf = _measure_source(lib_id, name, src, jobs)
        prefix = src["dir"].rsplit("/", 1)[-1] + "/"
        for r in rows:
            r["file"] = prefix + r["file"]
        for u in unf:
            u["def_file"], u["file"] = prefix + u["def_file"], prefix + u["file"]
        all_rows += rows
        all_unf += unf
        diag.update(meta["diagnostics"])
        metas.append({k: meta[k] for k in ("source", "root", "commit", "include", "exclude",
                                           "files", "toolchain", "missing_deps")})
    meta = {"backend": "source", "label": name, "library": lib_id,
            "root": du.display_path(REPOS),
            "files": sum(m["files"] for m in metas), "sources": metas,
            "diagnostics": dict(diag)}
    du.write_output(out, meta, all_rows, all_unf)


def measure_ilean(lib_id: str, name: str, sources: list[dict], jobs: int):
    import def_unfolds_ilean
    if len(sources) != 1:
        print(f"{lib_id}: the ilean backend runs on single-repository libraries", file=sys.stderr)
        return
    root, include, exclude = lake_root(sources[0])
    if not (root / ".lake/build/lib/lean").is_dir():
        print(f"{lib_id}: {du.display_path(root)} is not built (lake exe cache get, lake build)",
              file=sys.stderr)
        return
    libs = sorted({p.strip("/").split("/")[0] for p in include})
    uses = []
    meta, rows, unf = def_unfolds_ilean.run(root, libs, jobs, name, uses, include, exclude)
    meta.update({"library": lib_id, "source": sources[0]["dir"]})
    out = OUT / "ilean" / lib_id
    du.write_output(out, meta, rows, unf, uses)
    if (OUT / lib_id / "defs.jsonl").exists():
        (out / "comparison.md").write_text(du.compare(out, OUT / lib_id))


ORDER = ["mathlib", "tauceti", "lean-pool", "flt-anthropic", "formal-frontier", "openai-math",
         "axiom-cfsg"]


def table() -> str:
    names = {lib_id: name for lib_id, name, _ in libraries()}
    out = ["# Explicit unfoldings of definitions, by library", "",
           "Source backend of [def_unfolds.py](../../scripts/def_unfolds.py) on every "
           "`def`/`abbrev` of each library, in the scope of the other audits. A definition is "
           "*used* in a scope when its name occurs there, and *unfolded* there when it occurs "
           "in `unfold`/`delta`/`unseal`, as a bare item of a `simp`-like or `rw`-like list, "
           "or through an equation lemma (`foo.eq_def`). The directory of a definition includes "
           "its subdirectories. Every definition is counted (no sampling).", "",
           "Against Lean's own name resolution ([README](README.md)), the source backend finds "
           "about 99% of the unfoldings, with about 99% precision, but misses part of the uses "
           "(field notation on expressions, overloaded names): the counts of definitions used and "
           "of uses are lower bounds, so the shares and rates per use are slightly high.", ""]
    rows = []
    for lib_id in ORDER:
        p = OUT / lib_id / "summary.json"
        if not p.exists():
            continue
        g = json.loads(p.read_text())["def/abbrev"]
        meta = json.loads((OUT / lib_id / "meta.json").read_text())
        rows.append((names.get(lib_id, lib_id), meta, g))
    for label, key in (("Outside the definition's file", "outside_file"),
                       ("Outside the definition's directory", "outside_dir")):
        out += [f"## {label}", "",
                "| Library | Files | Definitions | Used there | Unfolded there | Share | "
                "Uses | Unfoldings | unfold | simp | rw | eq_def | Per 100 uses |",
                "|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|"]
        for name, meta, g in rows:
            s = g[key]
            u = s["unfoldings"]
            per = f"{100 * s['total_unfoldings'] / s['uses']:.2f}" if s["uses"] else "–"
            out.append(f"| {name} | {meta['files']:,} | {g['definitions']:,} | {s['used']:,} | "
                       f"{s['unfolded']:,} | {du._pct(s['unfolded'], s['used'])} | "
                       f"{s['uses']:,} | {s['total_unfoldings']:,} | {u['unfold']:,} | "
                       f"{u['simp']:,} | {u['rw']:,} | {u['eq_def']:,} | {per} |")
        out.append("")
    exact = [(name, lib_id) for lib_id in ORDER for name, meta, _ in rows
             if meta.get("library") == lib_id and (OUT / "ilean" / lib_id / "summary.json").exists()]
    if exact:
        out += ["## Exact counts for the built libraries", "",
                "Lean's own name resolution (ilean backend, on the `.ilean` files of a build "
                "restored from the library's cache at the same commit), next to the source "
                "backend. The unfoldings agree; the source backend misses part of the uses, "
                "so its shares and rates per use are higher. Comparisons in "
                + ", ".join(f"[ilean/{lib_id}/comparison.md](ilean/{lib_id}/comparison.md)"
                            for _, lib_id in exact) + ".", "",
                "| Library | Backend | Used outside file | Unfolded there | Share | Per 100 uses | "
                "Used outside directory | Unfolded there | Share | Per 100 uses |",
                "|---|---|---:|---:|---:|---:|---:|---:|---:|---:|"]
        for name, lib_id in exact:
            for backend, d in (("Lean", OUT / "ilean" / lib_id), ("source", OUT / lib_id)):
                g = json.loads((d / "summary.json").read_text())["def/abbrev"]
                cells = []
                for key in ("outside_file", "outside_dir"):
                    s = g[key]
                    per = f"{100 * s['total_unfoldings'] / s['uses']:.2f}" if s["uses"] else "–"
                    cells += [f"{s['used']:,}", f"{s['unfolded']:,}",
                              du._pct(s["unfolded"], s["used"]), per]
                out.append(f"| {name} | {backend} | " + " | ".join(cells) + " |")
        out.append("")
    out += ["Sources: " + "; ".join(
        f"{name} `{(meta.get('commit') or '')[:12]}`" if "sources" not in meta else
        f"{name} ({len(meta['sources'])} repositories)" for name, meta, _ in rows) + ".", ""]
    notes = []
    for name, meta, _ in rows:
        for m in meta.get("sources", [meta]):
            if "used)" in m.get("toolchain", ""):
                notes.append(f"{name} `{m.get('source', '')}`: {m['toolchain']}")
            if m.get("missing_deps"):
                notes.append(f"{name} `{m.get('source', '')}`: missing dependency sources "
                             + ", ".join(Path(d).name for d in m["missing_deps"]))
    if notes:
        out += ["Notes:", ""] + [f"- {n}" for n in notes] + [""]
    return "\n".join(out)


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--fetch", action="store_true", help="clone the pinned packages")
    ap.add_argument("--table", action="store_true", help="only rebuild the comparison table")
    ap.add_argument("--ilean", action="store_true",
                    help="ilean backend on the built libraries, compared with the source backend")
    ap.add_argument("--save-uses", action="store_true", help="also write every use (uses.jsonl)")
    ap.add_argument("--only", nargs="*", default=[], help="library ids")
    ap.add_argument("--jobs", type=int, default=24)
    a = ap.parse_args()
    only = set(a.only)
    if a.fetch:
        do_fetch(only)
        return
    if a.ilean:
        for lib_id, name, sources in libraries():
            if not only or lib_id in only:
                measure_ilean(lib_id, name, sources, a.jobs)
        return
    if not a.table:
        for lib_id, name, sources in libraries():
            if not only or lib_id in only:
                measure(lib_id, name, sources, a.jobs, a.save_uses)
    text = table()
    (OUT / "library-comparison.md").write_text(text)
    print(text)


if __name__ == "__main__":
    main()
