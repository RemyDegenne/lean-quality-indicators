"""Compression ratio of each corpus library: how redundant its source text is.

    python3 scripts/compression.py                       # every library
    python3 scripts/compression.py --only mathlib tauceti
    python3 scripts/compression.py --table               # only rebuild results.md

The files are those of the other audits (`include`/`exclude` of libraries.toml, OpenAI Math,
CFSG), in path order. Each library is measured twice: as is (`text`), and as code only
(`code`: comments and string literals removed, then trailing spaces and blank lines). The
ratio is original size / compressed size, with zstd at level 19, at five scales:

- per file: each file compressed alone (repetition inside a file);
- 64 KB, 1 MB, 8 MB chunks: the files concatenated in path order and cut into chunks of that
  size, each compressed alone (repetition across neighbouring files). The last, partial
  chunk is dropped. The chunks have the same size in every library, so these ratios do not
  depend on the library's size;
- whole library: everything at once, with a window covering the library. This ratio grows
  with the size of the library; the compressed size estimates its information content.

Alongside, a direct count of repetition across files: the share of code lines (at least 40
characters once stripped, other than `import`, `set_option` and `open` lines) that occur
verbatim in another file of the library.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
import multiprocessing as mp
import statistics
import sys
import time
from collections import Counter
from pathlib import Path

import zstandard as zstd

import def_unfolds as du
import def_unfolds_corpus as corpus
import leanscan as ls

OUT = corpus.ROOT / "runs/compression-2026-11-03"
LEVEL = 19
CHUNKS = {"64 KB": 1 << 16, "1 MB": 1 << 20, "8 MB": 1 << 23}
VARIANTS = ("text", "code")
FRAME = dict(write_checksum=False, write_content_size=False, write_dict_id=False)
TOP_MIN_BYTES = 8_000   # files listed among the most compressible
LINE_MIN_CHARS = 40
SKIP_LINES = ("import ", "public import ", "set_option ", "open ")
BLOBS: dict[str, bytes] = {}


def code_only(text: str) -> str:
    """Comments and string literals removed, then trailing spaces and blank lines."""
    masked, _ = ls.mask(text)
    return "".join(line.rstrip() + "\n" for line in masked.split("\n") if line.strip())


def line_hashes(code: str) -> list[int]:
    """Hashes of the code lines counted for repetition across files."""
    out = []
    for line in code.split("\n"):
        s = line.strip()
        if len(s) >= LINE_MIN_CHARS and not s.startswith(SKIP_LINES):
            out.append(int.from_bytes(hashlib.blake2b(s.encode(), digest_size=8).digest(),
                                      "little"))
    return out


def csize(data: bytes) -> int:
    return len(zstd.ZstdCompressor(level=LEVEL, **FRAME).compress(data))


def _file_job(path: str):
    raw = Path(path).read_bytes()
    text = code_only(raw.decode("utf-8", "replace"))
    code = text.encode()
    return path, raw, code, csize(raw), csize(code), line_hashes(text)


def _chunk_job(job):
    variant, size, i = job
    return variant, size, csize(BLOBS[variant][i * size:(i + 1) * size])


def _whole_job(variant: str):
    data = BLOBS[variant]
    t = time.time()
    params = zstd.ZstdCompressionParameters.from_level(
        LEVEL, window_log=max(20, min(31, math.ceil(math.log2(max(len(data), 2))))),
        enable_ldm=True, **FRAME)
    n = len(zstd.ZstdCompressor(compression_params=params).compress(data))
    return variant, n, time.time() - t


def files_of(sources: list[dict]) -> list[tuple[str, Path]]:
    """(display path, file) in path order; a library of several repositories prefixes its
    paths with the repository."""
    out = []
    for src in sources:
        root = corpus.REPOS / src["dir"]
        prefix = src["dir"].rsplit("/", 1)[-1] + "/" if len(sources) > 1 else ""
        out += [(prefix + rel, root / rel)
                for rel in du.list_files(root, src["include"], src["exclude"])]
    return sorted(out)


def ratio(raw: int, comp: int) -> float:
    return round(raw / comp, 3) if comp else 0.0


def measure(lib_id: str, name: str, sources: list[dict], jobs: int) -> dict:
    t0 = time.time()
    files = files_of(sources)
    display = {str(p): d for d, p in files}
    print(f"== {lib_id}: {len(files):,} files", file=sys.stderr)
    ctx = mp.get_context("fork")
    rows = {}
    with ctx.Pool(jobs) as pool:
        for path, raw, code, rc, cc, hashes in pool.imap_unordered(
                _file_job, [str(p) for _, p in files], chunksize=64):
            rows[display[path]] = (raw, code, rc, cc, hashes)
    order = [d for d, _ in files]
    BLOBS["text"] = b"".join(rows[d][0] for d in order)
    BLOBS["code"] = b"".join(rows[d][1] for d in order)
    files_with = Counter()
    for d in order:
        files_with.update(set(rows[d][4]))
    per_file = [{"file": d, "text": len(rows[d][0]), "text_compressed": rows[d][2],
                 "code": len(rows[d][1]), "code_compressed": rows[d][3],
                 "lines": len(rows[d][4]),
                 "lines_in_another_file": sum(files_with[h] > 1 for h in rows[d][4])}
                for d in order]
    del files_with
    seen, identical, identical_bytes = set(), 0, 0
    for d in order:
        h = hashlib.sha256(rows[d][0]).digest()
        if h in seen:
            identical += 1
            identical_bytes += len(rows[d][0])
        seen.add(h)
    del rows
    print(f"   read and compressed per file in {time.time() - t0:.0f} s", file=sys.stderr)

    chunk_sizes = {(v, s): [] for v in VARIANTS for s in CHUNKS.values()}
    jobs_list = [(v, s, i) for s in CHUNKS.values() for v in VARIANTS
                 for i in range(len(BLOBS[v]) // s)]
    with ctx.Pool(jobs) as pool:
        whole = [pool.apply_async(_whole_job, (v,)) for v in VARIANTS]
        for v, s, n in pool.imap_unordered(_chunk_job, jobs_list, chunksize=4):
            chunk_sizes[v, s].append(n)
        whole = {v: (n, secs) for v, n, secs in (w.get() for w in whole)}

    lines = sum(r["lines"] for r in per_file)
    shared = sum(r["lines_in_another_file"] for r in per_file)
    summary = {"library": lib_id, "name": name, "files": len(order),
               "identical_files": identical, "identical_bytes": identical_bytes,
               "lines": {"counted": lines, "in_another_file": shared,
                         "share": round(shared / lines, 4) if lines else 0.0}}
    for v in VARIANTS:
        raw = len(BLOBS[v])
        comp_files = sum(r[f"{v}_compressed"] for r in per_file)
        m = {"bytes": raw, "per_file": {"compressed": comp_files, "ratio": ratio(raw, comp_files)}}
        for label, s in CHUNKS.items():
            sizes = chunk_sizes[v, s]
            if not sizes:
                m[label] = None
                continue
            rs = sorted(s / n for n in sizes)
            q = (lambda f: round(rs[min(len(rs) - 1, int(f * len(rs)))], 3))
            m[label] = {"chunks": len(sizes), "ratio": ratio(s * len(sizes), sum(sizes)),
                        "p10": q(0.1), "median": round(statistics.median(rs), 3), "p90": q(0.9)}
        n, secs = whole[v]
        m["whole"] = {"compressed": n, "ratio": ratio(raw, n), "seconds": round(secs)}
        summary[v] = m
    meta = {"library": lib_id, "name": name, "level": LEVEL, "zstd": zstd.ZSTD_VERSION,
            "python_zstandard": zstd.__version__, "chunks": CHUNKS,
            "sources": [{"dir": s["dir"], "commit": du.git_commit(corpus.REPOS / s["dir"]),
                         "include": s["include"], "exclude": s["exclude"]} for s in sources],
            "seconds": round(time.time() - t0)}
    out = OUT / lib_id
    out.mkdir(parents=True, exist_ok=True)
    (out / "summary.json").write_text(json.dumps(summary, indent=1) + "\n")
    (out / "meta.json").write_text(json.dumps(meta, indent=1) + "\n")
    with open(out / "files.jsonl", "w") as f:
        for r in per_file:
            f.write(json.dumps(r) + "\n")
    BLOBS.clear()
    print(f"   done in {time.time() - t0:.0f} s", file=sys.stderr)
    return summary


def _fmt_mb(b: int) -> str:
    return f"{b / 1e6:,.1f}"


def _r(m) -> str:
    return f"{m['ratio']:.2f}" if m else "–"


def table() -> str:
    names = {lib_id: name for lib_id, name, _ in corpus.libraries()}
    libs = [lib for lib in corpus.ORDER if (OUT / lib / "summary.json").exists()]
    S = {lib: json.loads((OUT / lib / "summary.json").read_text()) for lib in libs}
    M = {lib: json.loads((OUT / lib / "meta.json").read_text()) for lib in libs}
    out = ["# Compression ratio, by library", "",
           "[compression.py](../../scripts/compression.py) on the files of each library, in the "
           "scope of the other audits. Ratio = original size / compressed size (zstd level "
           f"{LEVEL}); higher means more repetitive. *Code only*: comments and string literals "
           "removed, then trailing spaces and blank lines. Chunks: the files concatenated in "
           "path order, cut into chunks of a fixed size, each compressed alone; these ratios do "
           "not depend on the library's size, unlike the whole-library one.", ""]
    for v, title in (("text", "Source as is"), ("code", "Code only")):
        out += [f"## {title}", "",
                "| Library | Files | MB | Per file | 64 KB chunks | 1 MB chunks | 8 MB chunks "
                "| Whole library | Compressed MB |",
                "|---|---:|---:|---:|---:|---:|---:|---:|---:|"]
        for lib in libs:
            m = S[lib][v]
            out.append(f"| {names[lib]} | {S[lib]['files']:,} | {_fmt_mb(m['bytes'])} "
                       f"| {_r(m['per_file'])} | {_r(m['64 KB'])} | {_r(m['1 MB'])} "
                       f"| {_r(m['8 MB'])} | {_r(m['whole'])} "
                       f"| {_fmt_mb(m['whole']['compressed'])} |")
        out.append("")
    out += ["## Spread across 1 MB chunks (code only)", "",
            "| Library | Chunks | 10th percentile | Median | 90th percentile |",
            "|---|---:|---:|---:|---:|"]
    for lib in libs:
        m = S[lib]["code"]["1 MB"]
        if m:
            out.append(f"| {names[lib]} | {m['chunks']:,} | {m['p10']:.2f} | {m['median']:.2f} "
                       f"| {m['p90']:.2f} |")
    out += ["", "## Other measures", "",
            f"*Lines in another file*: share of the code lines (at least {LINE_MIN_CHARS} "
            "characters once stripped, other than `import`, `set_option` and `open` lines) that "
            "occur verbatim in another file of the library.", "",
            "| Library | Code lines counted | Lines in another file "
            "| Comments and blank lines (share of bytes) | Identical files |",
            "|---|---:|---:|---:|---:|"]
    for lib in libs:
        s = S[lib]
        out.append(f"| {names[lib]} | {s['lines']['counted']:,} | {s['lines']['share']:.1%} "
                   f"| {1 - s['code']['bytes'] / s['text']['bytes']:.1%} "
                   f"| {s['identical_files']:,} |")
    out += ["", f"## Most compressible files (code only, at least {TOP_MIN_BYTES // 1000} KB "
            "of code)", ""]
    for lib in libs:
        rows = []
        p = OUT / lib / "files.jsonl"
        if p.exists():
            with open(p) as f:
                rows = [r for r in map(json.loads, f) if r["code"] >= TOP_MIN_BYTES]
        rows.sort(key=lambda r: -r["code"] / r["code_compressed"])
        out += [f"### {names[lib]}", "", "| File | KB of code | Ratio |", "|---|---:|---:|"]
        out += [f"| `{r['file']}` | {r['code'] / 1e3:,.1f} | {r['code'] / r['code_compressed']:.1f} |"
                for r in rows[:10]]
        out.append("")
    commits = []
    for lib in libs:
        srcs = M[lib]["sources"]
        commits.append(f"{names[lib]} `{srcs[0]['commit'][:12]}`" if len(srcs) == 1
                       else f"{names[lib]} ({len(srcs)} repositories)")
    out += ["Sources: " + "; ".join(commits) + ".", ""]
    return "\n".join(out)


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--only", nargs="*", default=[])
    ap.add_argument("--jobs", type=int, default=mp.cpu_count())
    ap.add_argument("--table", action="store_true", help="only rebuild results.md")
    a = ap.parse_args(argv)
    if not a.table:
        for lib_id, name, sources in corpus.libraries():
            if a.only and lib_id not in a.only:
                continue
            missing = [s["dir"] for s in sources if not (corpus.REPOS / s["dir"]).exists()]
            if missing:
                print(f"{lib_id}: missing sources {missing}", file=sys.stderr)
                continue
            measure(lib_id, name, sources, a.jobs)
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / "results.md").write_text(table())


if __name__ == "__main__":
    main()
