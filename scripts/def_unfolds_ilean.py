"""Reference backend of def_unfolds.py: Lean's own name resolution, from `.ilean` files.

Lake writes, next to each compiled module, a reference index (`.ilean`): the declarations
of the module with their source ranges, and for every constant the module uses, the
module that defines it and the range of each use. The names are resolved by Lean, field
notation and `open` included, so this backend is the reference for the source backend.
It needs the library to be built, and the build to match the sources.

A definition's kind is the keyword before its name in the source. A use is kept only if
the source text at its range ends with the constant's last name component: this drops
uses through notation (which the source backend cannot see either) and uses in modules
whose source changed after the build. A module where fewer than half of all recorded
uses match the source is reported as stale (`meta.json`), and `compare` leaves it out.
"""
from __future__ import annotations

import bisect
import json
import multiprocessing as mp
import re
import sys
from collections import Counter
from pathlib import Path

import leanscan as ls
from def_unfolds import DEF_KINDS, EQN, aggregate, classify, display_path, git_commit

KEYWORD = re.compile(r"(?<![\w.'])(theorem|lemma|def|abbrev|instance|structure|class|"
                     r"inductive|coinductive|opaque|axiom|irreducible_def|alias|example)"
                     r"(?![\w'!?])")
STALE_BELOW = 0.5

DEFS: dict[str, tuple] = {}   # definition name -> (file, kind, line)
ROOT = Path(".")
BUILD = Path(".")


class Source:
    """A module's source, with LSP (line, UTF-16 column) to offset conversion."""

    def __init__(self, path: Path):
        self.text = path.read_text(errors="replace")
        self.masked, _ = ls.mask(self.text)
        self.starts = [0] + [m.end() for m in re.finditer("\n", self.text)]

    def offset(self, line: int, col: int) -> int:
        if line >= len(self.starts):
            return len(self.text)
        i = self.starts[line]
        end = self.starts[line + 1] if line + 1 < len(self.starts) else len(self.text)
        units = 0
        while i < end and units < col:
            units += 2 if ord(self.text[i]) > 0xFFFF else 1
            i += 1
        return i


def module_file(module: str) -> str:
    return module.replace(".", "/") + ".lean"


def _last(name: str) -> str:
    return name.rsplit(".", 1)[-1].replace("«", "").replace("»", "")


def _text_matches(src: Source, s: int, e: int, name: str) -> bool:
    t = src.text[s:e].replace("«", "").replace("»", "")
    return t.endswith(_last(name))


def _decls_job(ilean: str):
    data = json.loads(Path(ilean).read_text())
    rel = module_file(data["module"])
    path = ROOT / rel
    if not path.exists():
        return rel, [], Counter({"module without source": 1})
    src = Source(path)
    out, diag = [], Counter()
    for name, r in data.get("decls", {}).items():
        if name.startswith("_private.") or len(r) < 8:
            continue
        full_s, sel_s, sel_e = src.offset(r[0], r[1]), src.offset(r[4], r[5]), src.offset(r[6], r[7])
        if not _text_matches(src, sel_s, sel_e, name):
            diag["declaration range not on its name"] += 1
            continue
        kws = KEYWORD.findall(src.masked[full_s:sel_s])
        kind = kws[-1] if kws else None
        if kind in DEF_KINDS:
            out.append((name, kind, r[4] + 1))
    # Some declarations are missing from `decls` but have a definition range among the
    # references; their keyword is then read on the line of the name.
    module = data["module"]
    for key, ref in data.get("references", {}).items():
        d = ref.get("definition")
        if not d or not key.startswith('{"c"'):
            continue
        c = json.loads(key)["c"]
        name = c["n"]
        if c["m"] != module or name in data.get("decls", {}) or name.startswith("_private."):
            continue
        sel_s, sel_e = src.offset(d[0], d[1]), src.offset(d[2], d[3])
        if not _text_matches(src, sel_s, sel_e, name):
            continue
        kws = KEYWORD.findall(src.masked[src.starts[d[0]]:sel_s])
        if kws and kws[-1] in DEF_KINDS:
            out.append((name, kws[-1], d[0] + 1))
            diag["definition found through its references"] += 1
    return rel, out, diag


def _uses_job(ilean: str):
    data = json.loads(Path(ilean).read_text())
    rel = module_file(data["module"])
    path = ROOT / rel
    if not path.exists():
        return rel, [], Counter(), (0, 0)
    src = Source(path)
    occ, diag, seen = [], Counter(), set()
    checked = matched = 0
    for key, ref in data.get("references", {}).items():
        if not key.startswith('{"c"'):
            continue
        name = json.loads(key)["c"]["n"]
        for u in ref.get("usages", ()):
            s, e = src.offset(u[0], u[1]), src.offset(u[2], u[3])
            ok = _text_matches(src, s, e, name)
            checked += 1
            matched += ok
            target, forced = name, None
            if name not in DEFS:
                m = EQN.match(name)
                if not (m and m.group(1) in DEFS):
                    continue
                target, forced = m.group(1), "eq_def"
            if not ok:
                diag["use range not on the name (notation or stale)"] += 1
                continue
            if (target, s) in seen:
                continue
            seen.add((target, s))
            cat = forced or classify(src.masked, s, e)
            occ.append((target, DEFS[target][0], u[0] + 1, cat))
    return rel, occ, diag, (checked, matched)


def run(root: Path, libs: list[str], jobs: int, label: str = "", uses: list | None = None):
    global ROOT, BUILD
    ROOT, BUILD = root, root / ".lake/build/lib/lean"
    ileans = sorted(str(p) for lib in libs
                    for p in [BUILD / f"{lib}.ilean", *(BUILD / lib).rglob("*.ilean")]
                    if p.exists())
    print(f"modules: {len(ileans):,}", file=sys.stderr)
    ctx = mp.get_context("fork")
    diag = Counter()
    defs = {}
    with ctx.Pool(jobs) as pool:
        for rel, out, d in pool.imap_unordered(_decls_job, ileans, chunksize=16):
            diag.update(d)
            for name, kind, line in out:
                DEFS[name] = (rel, kind, line)
                defs[name, rel] = {"kind": kind, "line": line}
    print(f"definitions: {len(defs):,}", file=sys.stderr)
    occurrences, stale, files = [], [], 0
    with ctx.Pool(jobs) as pool:
        for rel, occ, d, (checked, matched) in pool.imap_unordered(_uses_job, ileans,
                                                                     chunksize=16):
            files += 1
            diag.update(d)
            if checked and matched / checked < STALE_BELOW:
                stale.append(rel)
            occurrences += [(n, df, rel, line, cat) for n, df, line, cat in occ]
    if stale:
        print(f"stale modules (index does not match the source): {len(stale):,}",
              file=sys.stderr)
    rows, unfoldings = aggregate(defs, occurrences, uses)
    meta = {"backend": "ilean", "label": label, "root": display_path(root),
            "commit": git_commit(root),
            "libs": libs, "files": files, "stale_files": sorted(stale),
            "diagnostics": dict(diag)}
    return meta, rows, unfoldings


if __name__ == "__main__":
    import def_unfolds
    def_unfolds.main(["ilean", *sys.argv[1:]])
