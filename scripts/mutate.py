"""Build a mutation test for a definition indicator.

    python3 scripts/mutate.py --spec indicators/definition-fidelity/mutations.json --run defs-mutants

For each source repository named in the spec, makes a hardlinked copy under repos/work/<dir>
(the originals are never written to), applies the spec's one-line mutations there, and writes
runs/<run>/samples.jsonl with the mutants and the unchanged controls, judged in the copies.
Which sample is a mutant is recorded in runs/<run>/key.json, outside the judges' reach. Then:

    python3 scripts/judge.py --run defs-mutants --indicator definition-fidelity
    python3 scripts/mutate.py --spec ... --run defs-mutants --score
"""

from __future__ import annotations

import argparse
import json
import random
import shutil
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import leanscan  # noqa: E402
import sample  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent
REPOS = ROOT / "repos"
WORK = "work"  # neutral name: the judges see paths under it


def copy_repo(src_dir: str) -> Path:
    dst = REPOS / WORK / src_dir
    if not dst.exists():
        dst.parent.mkdir(parents=True, exist_ok=True)
        subprocess.run(["cp", "-al", str(REPOS / src_dir), str(dst)], check=True)
        shutil.rmtree(dst / ".git", ignore_errors=True)  # removes the copy's links only
    return dst


def find_decl(text: str, src_cfg: dict, line: int):
    ths, docs = leanscan.scan(text, set(src_cfg.get("context_commands", [])),
                              set(src_cfg.get("other_commands", [])),
                              kinds=leanscan.DEFINITION_KW)
    match = [t for t in ths if t.cmd.line == line]
    if len(match) != 1:
        sys.exit(f"no definition at line {line}")
    return match[0], docs


def build(spec: dict, run: Path) -> None:
    cfg, _ = sample.load_config()
    src_cfg = {s["dir"]: s for lib in cfg["library"] for s in lib["source"]}
    lib_of = {s["dir"]: lib["id"] for lib in cfg["library"] for s in lib["source"]}
    items = [dict(m, mutated=True) for m in spec["mutants"]] + \
            [dict(c, mutated=False) for c in spec["controls"]]
    for it in items:
        copy_repo(it["dir"])
    # Apply the mutations (unlink first: the copy's files are hardlinks to the originals).
    for m in spec["mutants"]:
        p = REPOS / WORK / m["dir"] / m["path"]
        text = p.read_text(encoding="utf-8")
        decl, _ = find_decl(text, src_cfg[m["dir"]], m["line"])
        span = text[decl.cmd.start:decl.cmd.end]
        if span.count(m["old"]) != 1:
            if span.count(m["new"]) == 1:
                continue  # already applied
            sys.exit(f"{m['path']}:{m['line']}: `{m['old']}` must occur once in the definition")
        new_text = text[:decl.cmd.start] + span.replace(m["old"], m["new"]) + text[decl.cmd.end:]
        p.unlink()
        p.write_text(new_text, encoding="utf-8")
    random.Random("mutants").shuffle(items)  # mutants and controls interleaved
    run.mkdir(parents=True, exist_ok=True)
    out, key, count = [], {}, {}
    for it in items:
        d = f"{WORK}/{it['dir']}"
        text = (REPOS / d / it["path"]).read_text(encoding="utf-8")
        decl, docs = find_decl(text, src_cfg[it["dir"]], it["line"])
        lib = lib_of[it["dir"]]
        k = count[lib] = count.get(lib, -1) + 1
        sid = f"{lib}-{k:04d}"
        rel = f"samples/{lib}/{sid}.lean"
        (run / rel).parent.mkdir(parents=True, exist_ok=True)
        (run / rel).write_text(leanscan.render_context(text, docs, decl, keep_docs=True))
        name = decl.full_name
        out.append({"id": sid, "lib": lib, "dir": d, "path": it["path"], "line": it["line"],
                    "end_line": decl.end_line, "name": name, "keyword": decl.cmd.head,
                    "url": "", "file": rel, "has_docstring": True})
        key[sid] = {"mutated": it["mutated"], "name": name, "note": it.get("note", "")}
    with (run / "samples.jsonl").open("w") as f:
        for r in out:
            f.write(json.dumps(r, ensure_ascii=False) + "\n")
    (run / "key.json").write_text(json.dumps(key, indent=1, ensure_ascii=False) + "\n")
    (run / "run.json").write_text(json.dumps({"kind": "definitions", "keep_docstrings": True,
                                              "mutation_spec": True}, indent=1) + "\n")
    print(f"wrote {len(out)} samples ({len(spec['mutants'])} mutants) to {run}")


def score(run: Path, indicator: str, label: str) -> None:
    key = json.loads((run / "key.json").read_text())
    res = run / indicator / label / "results"
    rows = []
    for sid, k in key.items():
        p = res / f"{sid}.json"
        r = json.loads(p.read_text()) if p.exists() else {"verdict": "(not judged)"}
        rows.append((k["mutated"], sid, k["name"], r["verdict"], k["note"]))
    mut = [r for r in rows if r[0]]
    ctl = [r for r in rows if not r[0]]
    caught = sum(r[3] == "incorrect" for r in mut)
    print(f"mutants answered `incorrect`: {caught}/{len(mut)}; "
          f"controls answered `faithful`: {sum(r[3] == 'faithful' for r in ctl)}/{len(ctl)}")
    for m, sid, name, v, note in sorted(rows):
        print(f"  {'mutant ' if m else 'control'} {sid:16} {name[-45:]:45} -> {v:26} {note}")


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--spec", required=True)
    ap.add_argument("--run", required=True)
    ap.add_argument("--score", action="store_true", help="score the judged run against the key")
    ap.add_argument("--indicator", default="definition-fidelity")
    ap.add_argument("--label", default="claude-opus-5-5-high")
    args = ap.parse_args()
    run = ROOT / "runs" / args.run
    if args.score:
        score(run, args.indicator, args.label)
    else:
        build(json.loads(Path(args.spec).read_text()), run)


if __name__ == "__main__":
    main()
