"""Explicit unfoldings of definitions outside the file and directory that define them.

For each public `def`, `abbrev` and named `instance` of a library, count its uses and the
uses that unfold it explicitly, in three scopes: its own file, the rest of its directory
(subdirectories included), and everywhere else. A use unfolds the definition when it is

- `unfold`: an argument of `unfold`, `delta` or `unseal`, or of an
  `attribute [local semireducible]` command;
- `simp`: a bare item of the lemma list of `simp`, `dsimp`, `simp_all`, `simpa`,
  `field_simp`, `norm_num`, `push_cast` or `grind`, or an argument of `attribute [simp]`;
- `rw`: a bare item of the rule list of `rw`, `rwa`, `erw`, `rewrite`, `rw_mod_cast`,
  `nth_rw`, `nth_rewrite` or `simp_rw`;
- `eq_def`: one of its equation lemmas, `foo.eq_def`, `foo.eq_<n>` or `foo.eq_unfold`.

Unfolding through definitional equality (`show`, `change`, `rfl`, unification) leaves no
name behind and is not counted.

Two backends write the same output:

- `source` reads only the sources, so it needs no build and runs on CFSG. It resolves
  names with a syntactic version of Lean's rules: the namespaces in scope (including the
  declaration's own), the `open` commands, then the root namespace; a library declaration
  is visible only from the files that import its file, directly or not. Local binders
  shadow global names. A field-notation use `x.foo` counts when a binder gives the type
  of `x` (`(x : T ..)` gives `T.foo`), or else when `foo` is the last component of a
  single visible declaration, a definition. Field notation on other expressions, such as
  `(f x).foo`, needs type inference and is missed; uses that two opened namespaces make
  ambiguous are skipped. Neither is ever an explicit unfolding.
- `ilean` (def_unfolds_ilean.py) reads the reference index (`.ilean`) that Lake writes when
  it builds the library, so the names are resolved by Lean itself. It is the reference
  against which `compare` measures the source backend.

    python3 scripts/def_unfolds.py source --root repos/axiom-cfsg --include CFSG \\
        --exclude '*/Certificates/*' --deps repos/deps/*/ --deps CORE --out DIR
    python3 scripts/def_unfolds.py ilean --root ../mathlib4 --lib Mathlib --out DIR
    python3 scripts/def_unfolds.py compare REF_DIR OTHER_DIR

Each output directory holds `defs.jsonl` (one row per definition), `unfoldings.jsonl`
(one row per explicit unfolding), `summary.json`, `meta.json` and `report.md`.
"""
from __future__ import annotations

import argparse
import bisect
import fnmatch
import gc
import json
import multiprocessing as mp
import posixpath
import re
import subprocess
import sys
from collections import Counter, defaultdict
from pathlib import Path

import leanscan as ls

CATEGORIES = ("unfold", "simp", "rw", "eq_def")
SCOPES = ("file", "dir", "outside")
SCOPE_LABELS = {"file": "own file", "dir": "rest of directory", "outside": "outside directory"}
DEF_KINDS = {"def", "abbrev", "instance"}
GROUPS = {"def/abbrev": {"def", "abbrev"}, "instance": {"instance"}}
# Declarations whose names enter the name table.
DECL_HEADS = {
    "theorem", "lemma", "def", "abbrev", "instance", "structure", "class", "inductive",
    "coinductive", "opaque", "axiom", "irreducible_def", "alias",
}

_ID = r"(?:[^\W\d][\w'!?]*|«[^»]*»)"
NAME = rf"{_ID}(?:\.{_ID})*"
NAME_RE = re.compile(NAME)
EQN = re.compile(r"^(.+)\.(?:eq_def|eq_unfold|eq_\d+)$")


# ---------------------------------------------------------------------------------------
# Classification of one use (shared by both backends)

_BEFORE = r"(?:^|[\s(;·>{|])"
UNFOLD_HEAD = re.compile(rf"{_BEFORE}(?:unfold|delta|unseal)(?:\s+{NAME})*\s+$")
ATTRIBUTE_HEAD = re.compile(rf"^\s*attribute\s*\[([^\]]*)\](?:\s+{NAME})*\s+$")
REWRITE_TACTICS = ("rw", "rwa", "erw", "rewrite", "rw_mod_cast", "nth_rw", "nth_rewrite",
                   "simp_rw")
SIMP_TACTICS = ("simp", "simp_all", "simpa", "dsimp", "simp_arith", "simp_all_arith",
                "field_simp", "norm_num", "push_cast", "grind")
_TACTIC = "|".join(sorted(REWRITE_TACTICS + SIMP_TACTICS, key=len, reverse=True))
# Tactic keyword, then options (`only`, occurrence numbers, `(config := ...)`, `+arith`).
LIST_HEAD = re.compile(
    rf"{_BEFORE}({_TACTIC})[?!]*"
    r"(?:\s*(?:only\b|\d+|\((?:[^()]|\([^()]*\))*\)|[+-][\w.]+))*\s*$")


def _list_bracket(masked: str, start: int, end: int) -> int:
    """Offset of the `[` of the list of which masked[start:end] is a bare item, or -1."""
    n = len(masked)
    j = end
    while j < n and masked[j] in " \t\n":
        j += 1
    if j >= n or masked[j] not in ",]":
        return -1
    i = start - 1
    while i >= 0 and masked[i] in " \t\n":
        i -= 1
    if i >= 0 and masked[i] in "←↓↑":
        i -= 1
    elif i >= 1 and masked[i - 1:i + 1] == "<-":
        i -= 2
    while i >= 0 and masked[i] in " \t\n":
        i -= 1
    if i < 0:
        return -1
    if masked[i] == "[":
        return i
    if masked[i] != ",":
        return -1
    depth = 0
    for k in range(i - 1, max(-1, i - 5000), -1):
        c = masked[k]
        if c in ")]}⟩":
            depth += 1
        elif c in "([{⟨":
            if depth == 0:
                return k if c == "[" else -1
            depth -= 1
    return -1


def classify(masked: str, start: int, end: int) -> str | None:
    """Kind of explicit unfolding made by the name at masked[start:end], if any.

    `masked` is the file with comments and strings blanked (leanscan.mask)."""
    before = masked[masked.rfind("\n", 0, start) + 1:start]
    if UNFOLD_HEAD.search(before):
        return "unfold"
    m = ATTRIBUTE_HEAD.search(before)
    if m:
        if re.search(r"(?<![-\w])simp\b", m.group(1)):
            return "simp"
        if re.search(r"(?<![-\w])(?:semi)?reducible\b", m.group(1)):
            return "unfold"
        return None
    b = _list_bracket(masked, start, end)
    if b < 0:
        return None
    m = LIST_HEAD.search(masked[max(0, b - 300):b])
    if not m:
        return None
    return "rw" if m.group(1) in REWRITE_TACTICS else "simp"


# ---------------------------------------------------------------------------------------
# Aggregation and reports (shared)

def scope_of(def_file: str, use_file: str) -> str:
    if use_file == def_file:
        return "file"
    d = posixpath.dirname(def_file)
    return "dir" if not d or use_file.startswith(d + "/") else "outside"


def aggregate(defs: dict, occurrences, uses: list | None = None):
    """Per-definition rows and the list of explicit unfoldings.

    `defs` maps (name, file) to {"kind", "line"}; `occurrences` yields
    (name, def_file, use_file, line, category or None). Every use is also appended to
    `uses` when it is given."""
    rows = {key: {"name": key[0], "file": key[1], **info,
                  "uses": dict.fromkeys(SCOPES, 0),
                  "unfolds": {s: dict.fromkeys(CATEGORIES, 0) for s in SCOPES}}
            for key, info in defs.items()}
    files = defaultdict(set)
    unfoldings = []
    for name, def_file, use_file, line, cat in occurrences:
        r = rows.get((name, def_file))
        if r is None:  # a name declared in several files, not a definition in this one
            continue
        if uses is not None:
            uses.append((name, def_file, use_file, line))
        s = scope_of(def_file, use_file)
        r["uses"][s] += 1
        if cat:
            r["unfolds"][s][cat] += 1
            unfoldings.append({"def": name, "def_file": def_file, "file": use_file,
                               "line": line, "category": cat, "scope": s})
            files[name, def_file, s].add(use_file)
    for (name, def_file), r in rows.items():
        r["unfolding_files"] = {s: len(files[name, def_file, s]) for s in ("dir", "outside")}
    out = sorted(rows.values(), key=lambda r: (r["file"], r["line"], r["name"]))
    unfoldings.sort(key=lambda u: (u["file"], u["line"], u["def"]))
    return out, unfoldings


def _n_unfolds(r: dict, scopes) -> int:
    return sum(sum(r["unfolds"][s].values()) for s in scopes)


def summarize(rows: list[dict]) -> dict:
    out = {}
    for group, kinds in GROUPS.items():
        rs = [r for r in rows if r["kind"] in kinds]
        g = {"definitions": len(rs)}
        for label, scopes in (("own_file", ("file",)), ("outside_file", ("dir", "outside")),
                              ("outside_dir", ("outside",))):
            g[label] = {
                "used": sum(1 for r in rs if any(r["uses"][s] for s in scopes)),
                "unfolded": sum(1 for r in rs if _n_unfolds(r, scopes)),
                "uses": sum(r["uses"][s] for r in rs for s in scopes),
                "unfoldings": {c: sum(r["unfolds"][s][c] for r in rs for s in scopes)
                               for c in CATEGORIES},
            }
            g[label]["total_unfoldings"] = sum(g[label]["unfoldings"].values())
        out[group] = g
    return out


def _pct(a: int, b: int) -> str:
    return f"{100 * a / b:.1f}%" if b else "–"


def render_report(meta: dict, summary: dict, rows: list[dict], top: int = 30) -> str:
    out = [f"# Explicit unfoldings of definitions: {meta.get('label', '')}".rstrip(), ""]
    out.append(f"Backend: `{meta['backend']}`. Source: `{meta.get('root', '')}`"
               + (f" at `{meta['commit'][:12]}`" if meta.get("commit") else "") + ".")
    if meta.get("files") is not None:
        out.append(f"Files scanned: {meta['files']:,}.")
    out += ["", "An explicit unfolding is a use of the name in `unfold`/`delta`/`unseal` (unfold), "
            "a simp-like lemma list (simp), a rewrite rule list (rw), or an equation lemma "
            "`foo.eq_def`/`foo.eq_<n>` (eq_def). Scopes: the definition's own file, the rest of its "
            "directory (subdirectories included), and everything else.", ""]
    for group, g in summary.items():
        if not g["definitions"]:
            continue
        out += [f"## {group} ({g['definitions']:,} definitions)", "",
                "| Where | Definitions used | Definitions unfolded | Share unfolded | Uses "
                "| Unfoldings | unfold | simp | rw | eq_def | Unfoldings per 100 uses |",
                "|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|"]
        for label, title in (("own_file", "own file"), ("outside_file", "outside file"),
                             ("outside_dir", "outside directory")):
            s = g[label]
            u = s["unfoldings"]
            out.append(f"| {title} | {s['used']:,} | {s['unfolded']:,} | "
                       f"{_pct(s['unfolded'], s['used'])} | {s['uses']:,} | "
                       f"{s['total_unfoldings']:,} | {u['unfold']:,} | {u['simp']:,} | "
                       f"{u['rw']:,} | {u['eq_def']:,} | "
                       f"{100 * s['total_unfoldings'] / s['uses']:.2f} |" if s["uses"] else
                       f"| {title} | 0 | 0 | – | 0 | 0 | 0 | 0 | 0 | 0 | – |")
        out.append("")
    for label, scopes in (("outside its file", ("dir", "outside")),
                          ("outside its directory", ("outside",))):
        ranked = sorted((r for r in rows if r["kind"] in DEF_KINDS and _n_unfolds(r, scopes)),
                        key=lambda r: (-_n_unfolds(r, scopes), r["name"]))[:top]
        if not ranked:
            continue
        out += [f"## Most unfolded {label}", "",
                "| Definition | Kind | File | Unfoldings | Files | Uses there | Total uses |",
                "|---|---|---|---:|---:|---:|---:|"]
        for r in ranked:
            nfiles = sum(r["unfolding_files"][s] for s in scopes)
            out.append(f"| `{r['name']}` | {r['kind']} | `{r['file']}` | "
                       f"{_n_unfolds(r, scopes)} | {nfiles} | "
                       f"{sum(r['uses'][s] for s in scopes)} | {sum(r['uses'].values())} |")
        out.append("")
    if meta.get("diagnostics"):
        out += ["## Diagnostics", ""]
        out += [f"- {k}: {v:,}" for k, v in sorted(meta["diagnostics"].items())]
        out.append("")
    return "\n".join(out)


def write_output(out: Path, meta: dict, rows: list[dict], unfoldings: list[dict],
                 uses: list | None = None) -> dict:
    out.mkdir(parents=True, exist_ok=True)
    if uses is not None:
        with open(out / "uses.jsonl", "w") as f:
            for u in uses:
                f.write(json.dumps(u, ensure_ascii=False) + "\n")
    with open(out / "defs.jsonl", "w") as f:
        for r in rows:
            f.write(json.dumps(r, ensure_ascii=False) + "\n")
    with open(out / "unfoldings.jsonl", "w") as f:
        for u in unfoldings:
            f.write(json.dumps(u, ensure_ascii=False) + "\n")
    summary = summarize(rows)
    (out / "summary.json").write_text(json.dumps(summary, indent=1) + "\n")
    (out / "meta.json").write_text(json.dumps(meta, indent=1, ensure_ascii=False) + "\n")
    (out / "report.md").write_text(render_report(meta, summary, rows))
    return summary


REPO = Path(__file__).resolve().parent.parent


def display_path(path) -> str:
    """A path as written in outputs: relative to this repository (or to its parent
    directory, for sibling checkouts), or under `~`."""
    path = Path(path).resolve()
    if path.is_relative_to(REPO):
        return path.relative_to(REPO).as_posix() or "."
    if path.is_relative_to(REPO.parent):
        return "../" + path.relative_to(REPO.parent).as_posix()
    if path.is_relative_to(Path.home()):
        return "~/" + path.relative_to(Path.home()).as_posix()
    return str(path)


def git_commit(root: Path) -> str:
    r = subprocess.run(["git", "rev-parse", "HEAD"], cwd=root, capture_output=True, text=True)
    return r.stdout.strip() if r.returncode == 0 else ""


# ---------------------------------------------------------------------------------------
# Scopes: namespaces, `open` and local names in effect at each command

class Scope:
    def __init__(self):
        self.frames = [{"kind": "file", "names": [], "opens": [], "locals": {}}]

    def ns(self) -> list[str]:
        return [n for f in self.frames if f["kind"] == "namespace" for n in f["names"]]

    def opens(self) -> list[tuple]:
        return [o for f in self.frames for o in f["opens"]]

    def locals(self) -> dict:
        out = {}
        for f in self.frames:
            out.update(f["locals"])
        return out

    def enter(self, kind: str, name: str):
        parts = [p for p in name.replace("«", "").replace("»", "").split(".") if p]
        self.frames.append({"kind": kind, "names": parts, "opens": [], "locals": {}})

    def close(self, name: str):
        frames = self.frames
        if len(frames) == 1:
            return
        remaining = [p for p in name.split(".") if p]
        if not remaining:
            frames.pop()
            return
        while remaining and len(frames) > 1:
            f = frames[-1]
            k = len(f["names"])
            if k and k <= len(remaining) and f["names"] == remaining[-k:]:
                remaining = remaining[:-k]
                frames.pop()
            elif k and len(remaining) < k and f["names"][-len(remaining):] == remaining:
                f["names"] = f["names"][:-len(remaining)]
                remaining = []
            else:
                frames.pop()
                remaining = []


def _word_after(masked: str, cmd: ls.Command) -> str:
    rest = masked[cmd.head_pos + len(cmd.head):cmd.end].split()
    return rest[0] if rest else ""


def decl_name(masked: str, cmd: ls.Command):
    """(name, start, end) of the name a declaration command introduces, or None."""
    i = cmd.head_pos + len(cmd.head)
    if cmd.head == "class":
        m = re.compile(r"\s+inductive\b").match(masked, i)
        if m:
            i = m.end()
    while True:
        while i < cmd.end and masked[i].isspace():
            i += 1
        if masked.startswith("(priority", i) or masked.startswith("( priority", i):
            depth = 0
            while i < cmd.end:
                depth += {"(": 1, ")": -1}.get(masked[i], 0)
                i += 1
                if depth == 0:
                    break
            continue
        break
    m = NAME_RE.match(masked, i, cmd.end)
    if not m or m.group() in ("where", "extends"):
        return None
    return m.group(), m.start(), m.end()


def full_name(ns: list[str], name: str) -> str:
    name = name.replace("«", "").replace("»", "")
    if name.startswith("_root_."):
        return name[len("_root_."):]
    return ".".join(ns + [name]) if ns else name


_FIELD_LINE = re.compile(rf"^([ \t]+)({_ID})((?:[ \t]+{_ID})*)[ \t]*(?=[:({{\[⦃])", re.M)
_CTOR_LINE = re.compile(rf"^[ \t]*\|[ \t]*({_ID})", re.M)
_MK_LINE = re.compile(rf"^[ \t]+({_ID})[ \t]*::", re.M)


def structure_members(masked: str, cmd: ls.Command, full: str) -> list[tuple[str, str]]:
    """Fields and constructors a structure, class or inductive declares (approximate)."""
    text = masked[cmd.head_pos:cmd.end]
    out = []
    if cmd.head in ("inductive", "coinductive") or text.startswith("class inductive"):
        return [(f"{full}.{m.group(1)}", "ctor") for m in _CTOR_LINE.finditer(text)]
    w = re.search(r"\bwhere\b", text)
    if not w:
        return [(f"{full}.mk", "ctor")]
    body = text[w.end():]
    mk = _MK_LINE.search(body)
    out.append((f"{full}.{mk.group(1) if mk else 'mk'}", "ctor"))
    indent = None
    for m in _FIELD_LINE.finditer(body):
        if indent is None:
            indent = m.group(1)
        if m.group(1) != indent:
            continue
        for f in [m.group(2)] + m.group(3).split():
            out.append((f"{full}.{f}", "field"))
    return out


def scan_decls(path: Path, rel: str) -> dict:
    """Declarations, namespaces and imports of one file."""
    text = path.read_text(errors="replace")
    masked, docs = ls.mask(text)
    cmds = ls.split_commands(masked, docs, EXTRA_COMMANDS)
    line_starts = [0] + [m.end() for m in re.finditer("\n", masked)]
    scope = Scope()
    decls, members, namespaces, imports = [], [], set(), []
    for cmd in cmds:
        h = cmd.head
        if h == "namespace":
            scope.enter("namespace", _word_after(masked, cmd))
            namespaces.add(".".join(scope.ns()))
        elif h in ("section", "mutual"):
            scope.enter(h, _word_after(masked, cmd) if h == "section" else "")
        elif h == "end":
            scope.close(_word_after(masked, cmd))
        elif h == "import":
            words = masked[cmd.head_pos + len(h):cmd.end].split()
            if words and words[0] == "all":
                words = words[1:]
            imports.append(words[0] if words else "")
        elif h in DECL_HEADS:
            d = decl_name(masked, cmd)
            if not d or (h == "alias" and d[0].startswith("⟨")):
                continue
            full = full_name(scope.ns(), d[0])
            kind = "class" if h == "class" else h
            decls.append((full, kind, bisect.bisect_right(line_starts, d[1]),
                          "protected" in cmd.mods, "private" in cmd.mods))
            if h in ("structure", "class", "inductive", "coinductive"):
                members += structure_members(masked, cmd, full)
    return {"file": rel, "decls": decls, "members": members, "namespaces": sorted(namespaces),
            "imports": [i for i in imports if i]}


# ---------------------------------------------------------------------------------------
# Source backend: name tables (built in the parent, shared with forked workers)

LIB: dict[str, tuple] = {}         # public library name -> (kind, file, line, protected)
DUPS: dict[str, list] = {}         # names declared in several files -> [(kind, file, line, prot)]
PRIV: dict[str, dict] = {}         # file -> {private name: kind}
DEP: dict[str, bool] = {}          # dependency name -> protected
NAMESPACES: set[str] = set()
DEF_LAST: set[str] = set()         # last components of library definitions
LIB_LAST: dict[str, list] = {}     # last component -> library names (all kinds)
DEP_LAST: set[str] = set()
IMPORTS: dict[str, list] = {}      # library file -> library files it imports
EXTRA_COMMANDS: set[str] = set()   # library-defined commands (command starts)
ALIASES: dict[str, str] = {}       # aliases made by FLT's commands in the file being scanned
ROOT: Path = Path(".")
VISIBLE: set[str] = set()          # files transitively imported by the file being scanned


def _see(rel: str):
    """Make visible the library files that `rel` imports, directly or not, and itself."""
    VISIBLE.clear()
    VISIBLE.add(rel)
    stack = [rel]
    while stack:
        for g in IMPORTS.get(stack.pop(), ()):
            if g not in VISIBLE:
                VISIBLE.add(g)
                stack.append(g)


def _lib(name: str):
    """The visible library declaration `name`: (kind, file, line, protected), or None."""
    dups = DUPS.get(name)
    if dups:
        return next((d for d in dups if d[1] in VISIBLE), None)
    info = LIB.get(name)
    return info if info is not None and info[1] in VISIBLE else None


def _exists(c: str, atomic: bool, file: str) -> bool:
    if c in ALIASES:
        return True
    info = _lib(c)
    if info is not None:
        return not (atomic and info[3])
    p = DEP.get(c)
    if p is not None:
        return not (atomic and p)
    if c in PRIV.get(file, ()):
        return True
    m = EQN.match(c)
    return bool(m) and (_lib(m.group(1)) is not None or m.group(1) in DEP)


def resolve(parts: list[str], ns: list[str], opens: list[tuple], file: str):
    """Lean's resolveGlobalName on the name tables: (candidates, projections)."""
    for k in range(len(parts), 0, -1):
        idn = ".".join(parts[:k])
        atomic = k == 1
        for j in range(len(ns), 0, -1):  # innermost namespace first
            c = ".".join(ns[:j]) + "." + idn
            if _exists(c, atomic, file):
                return [ALIASES.get(c, c)], parts[k:]
        if not atomic:
            c = idn[len("_root_."):] if idn.startswith("_root_.") else idn
            if _exists(c, False, file):
                return [ALIASES.get(c, c)], parts[k:]
        found = []
        if atomic and _exists(idn, True, file):
            found.append(idn)
        for o in opens:
            if o[0] == "simple":
                if idn not in o[2]:
                    c = o[1] + "." + idn
                    if _exists(c, atomic, file):
                        found.append(c)
            elif o[1] == idn:
                found.append(o[2])
            elif idn.startswith(o[1] + "."):
                c = o[2] + idn[len(o[1]):]
                if _exists(c, False, file):
                    found.append(c)
        if found:
            return list(dict.fromkeys(ALIASES.get(c, c) for c in found)), parts[k:]
    return [], parts


def resolve_namespace(n: str, ns: list[str], opens: list[tuple]) -> list[str]:
    n = n.replace("«", "").replace("»", "")
    if n.startswith("_root_."):
        n = n[len("_root_."):]
        return [n]
    out = []
    for j in range(len(ns), -1, -1):
        c = ".".join(ns[:j] + [n])
        if c in NAMESPACES:
            out.append(c)
            break
    for o in opens:
        if o[0] == "simple":
            c = o[1] + "." + n
            if c in NAMESPACES and c not in out:
                out.append(c)
    return out or [n]


def parse_open(body: str, ns: list[str], opens: list[tuple]) -> list[tuple]:
    """Open declarations of `open <body>`: ("simple", ns, hidden) or ("explicit", id, target)."""
    body = body.strip()
    if not body or body.split()[0] in ("scoped", "private"):
        return []
    m = re.match(rf"({NAME})\s*\(([^)]*)\)\s*$", body, re.S)
    if m:
        targets = resolve_namespace(m.group(1), ns, opens)
        return [("explicit", x, f"{targets[0]}.{x}") for x in NAME_RE.findall(m.group(2))]
    m = re.match(rf"({NAME})\s+hiding\s+(.*)$", body, re.S)
    if m:
        hidden = frozenset(NAME_RE.findall(m.group(2)))
        return [("simple", t, hidden) for t in resolve_namespace(m.group(1), ns, opens)]
    m = re.match(rf"({NAME})\s+renaming\s+(.*)$", body, re.S)
    if m:
        target = resolve_namespace(m.group(1), ns, opens)[0]
        return [("explicit", new, f"{target}.{old}") for old, new in
                re.findall(rf"({NAME})\s*(?:→|->)\s*({NAME})", m.group(2))]
    out = []
    for n in NAME_RE.findall(body):
        out += [("simple", t, frozenset()) for t in resolve_namespace(n, ns, opens + out)]
    return out


_OPEN_IN = re.compile(r"(?<![\w.])open\s+(.*?)\s+in(?![\w'!?])", re.S)

# Local names, with the head of their type when a binder gives it: `(x : Foo a)` maps x
# to "Foo", so that `x.bar` resolves to `Foo.bar`.
_ATOM = re.compile(rf"(?<![\w.'!?]){_ID}(?![\w.'!?])")
_BINDER = re.compile(r"[(\{⦃\[]\s*((?:[^\W\d][\w'!?]*\s+)*[^\W\d][\w'!?]*)\s*:(?![=:])\s*")
_QUANT = re.compile(r"(?:∀|∃!?|Π|Σ|∑|∏|⋃|⋂|⨆|⨅)\s*([^,]*?),")
_FUN = re.compile(r"(?:\bfun\b|λ)([^=↦]*?)(?:=>|↦)", re.S)
_TACTIC_BINDERS = re.compile(
    r"\b(?:intro|intros|rintro|introv|ext|funext|choose!?|by_contra!?|obtain|set|let|have|"
    r"generalize|lift|by_cases|next|case|rename_i)\b([^\n;]*?)"
    r"(?=:=|:(?![=:])|=>|;|\busing\b|\n|$)")
_WITH = re.compile(r"\bwith\b([^\n;]*?)(?==>|:=|\busing\b|\n|$)")
_ALT = re.compile(r"^[ \t]*\|[ \t]*\.?[\w.'!?]+((?:[ \t]+[\w'!?⟨⟩,@_]+)*)[ \t]*=>", re.M)
_RELATION = re.compile(r"[∈∉⊆⊂⊇⊃<≤>≥≠]")
_TYPES = re.compile(r":[^()\[\]{}⟨⟩⦃⦄]*")


def _bracket_binders(text: str, out: dict):
    """Binder groups `(x y : T)` in `text`: each name mapped to the first name of T."""
    for m in _BINDER.finditer(text):
        depth, i = 0, m.end()
        while i < len(text):
            c = text[i]
            if c in "([{⦃⟨":
                depth += 1
            elif c in ")]}⦄⟩":
                if depth == 0:
                    break
                depth -= 1
            i += 1
        t = NAME_RE.match(text, m.end(), i)
        for n in m.group(1).split():
            out[n] = t.group() if t else None


def signature_end(masked: str, i: int, end: int) -> int:
    """End of a declaration's binders: the first `:` or `|` outside brackets."""
    depth = 0
    while i < end:
        c = masked[i]
        if c in "([{⦃⟨":
            depth += 1
        elif c in ")]}⦄⟩":
            depth -= 1
        elif depth == 0 and c in ":|":
            return i
        i += 1
    return end


def local_names(text: str, signature: str = "") -> dict:
    """Names bound in a command, mapped to their type head when known.

    Bracket binders are read only in `signature` (the declaration's binders) and in
    quantifiers: elsewhere `(f x : T)` is usually a type ascription."""
    out: dict = {}
    _bracket_binders(signature, out)
    for m in _QUANT.finditer(text):
        _bracket_binders(m.group(1), out)
        for n in _ATOM.findall(_RELATION.split(_TYPES.sub(" ", m.group(1)))[0]):
            out.setdefault(n, None)
    for m in _FUN.finditer(text):
        _bracket_binders(m.group(1), out)
        for n in _ATOM.findall(_TYPES.sub(" ", m.group(1))):
            out.setdefault(n, None)
    for rx in (_TACTIC_BINDERS, _WITH, _ALT):
        for m in rx.finditer(text):
            for n in _ATOM.findall(m.group(1)):
                out.setdefault(n, None)
    return out


TOKEN = re.compile(
    rf"(?<![\w.'!?@#$])@?({NAME})"                 # a name, possibly qualified
    rf"|(?<=[)\]}}⟩])\.({_ID})"                     # field notation after a closing bracket
    rf"|(?<![\w)\]}}⟩'!?.])\.({_ID})")              # leading-dot name `.foo`
_ATTR = re.compile(r"@\[")
_AFTER = re.compile(r"\s*(:=|:(?!:))")
_WORD_BEFORE = re.compile(r"([\w']+)[?!]*$")
NOT_USES = {"namespace", "section", "end", "mutual", "import", "open", "universe",
            "universes", "set_option", "include", "omit", "module", "export"}
LIST_WORDS = set(REWRITE_TACTICS + SIMP_TACTICS) | {"only"}


def _in_notation(masked: str, start: int, end: int) -> bool:
    """A name inside postfix bracket notation such as `R[X]` or `R⟦X⟧`."""
    if start < 2 or masked[start - 1] not in "[⟦" or masked[end:end + 1] not in ("]", "⟧", ";"):
        return False
    w = _WORD_BEFORE.search(masked, max(0, start - 40), start - 1)
    return bool(w) and w.group(1) not in LIST_WORDS


def _def_target(c: str):
    """(definition name, forced category) if `c` names a library definition or one of its
    equation lemmas; None otherwise."""
    info = _lib(c)
    if info is not None:
        return (c, None) if info[0] in DEF_KINDS else None
    m = EQN.match(c)
    if m:
        info = _lib(m.group(1))
        if info is not None and info[0] in DEF_KINDS:
            return m.group(1), "eq_def"
    return None


def _field_target(p: str):
    """The definition `x.p` refers to when only one declaration has last component `p`."""
    if p not in DEF_LAST or p in DEP_LAST:
        return None
    names = [n for n in LIB_LAST.get(p, ()) if _lib(n) is not None]
    return names[0] if len(names) == 1 and _lib(names[0])[0] in DEF_KINDS else None


def _field(p: str, head, locs: dict, ns, opens, file):
    """Definition used by field notation `x.p`, where x's type has head `head` (or None)."""
    if head and head.split(".")[0] not in locs:
        cands, projs = resolve(head.split("."), ns, opens, file)
        if len(cands) == 1 and not projs:
            c = cands[0] + "." + p
            if _lib(c) is not None or c in DEP:
                t = _def_target(c)
                return t[0] if t and not t[1] else None
    return _field_target(p)


def _def_file(name: str) -> str:
    """File of the visible definition `name` (its own file first, for repeated names)."""
    dups = DUPS.get(name)
    if dups:
        files = [d[1] for d in dups if d[1] in VISIBLE]
        return CURRENT[0] if CURRENT[0] in files else files[0]
    return LIB[name][1]


CURRENT = [""]


P2M_COMMANDS = {"p2m_open", "p2m_export", "p2m_alias", "p2m_open_scoped", "p2m_reactivate",
                "p2m_ns", "p2m_export_all"}


def _p2m(h: str, text: str, scope: Scope):
    """FLT's scoping commands (P2M/Util.lean), whose arguments are strings:
    `p2m_open "A B~hidden"` opens A and B (absolute names), `p2m_export "N" "a b"` makes
    `<current namespace>.a` an alias of `N.a`, `p2m_alias "a" "n"` makes `a` an alias of `n`.
    The others only activate scoped extensions or register namespaces."""
    args = re.findall(r'"([^"]*)"', text)
    if h == "p2m_open" and args:
        for w in args[0].split():
            parts = w.split("~")
            scope.frames[-1]["opens"].append(("simple", parts[0],
                                              frozenset(x for x in parts[1:] if x)))
    elif h == "p2m_export" and len(args) >= 2:
        cur = ".".join(scope.ns())
        for w in args[1].split():
            ALIASES[f"{cur}.{w}" if cur else w] = f"{args[0]}.{w}"
    elif h == "p2m_alias" and len(args) >= 2:
        ALIASES[args[0]] = args[1]


def scan_uses(rel: str):
    """Uses of library definitions in one file: [(name, def_file, line, category)]."""
    text = (ROOT / rel).read_text(errors="replace")
    masked, docs = ls.mask(text)
    cmds = ls.split_commands(masked, docs, EXTRA_COMMANDS)
    line_starts = [0] + [m.end() for m in re.finditer("\n", masked)]
    scope = Scope()
    occ, diag = [], Counter()
    ALIASES.clear()
    _see(rel)
    CURRENT[0] = rel
    for cmd in cmds:
        h = cmd.head
        if h == "namespace":
            scope.enter("namespace", _word_after(masked, cmd))
            continue
        if h in ("section", "mutual"):
            scope.enter(h, _word_after(masked, cmd) if h == "section" else "")
            continue
        if h == "end":
            scope.close(_word_after(masked, cmd))
            continue
        if h == "import":
            continue
        if h in P2M_COMMANDS and h in EXTRA_COMMANDS:
            # The arguments are strings, blanked in `masked`: read the whole line.
            eol = text.find("\n", cmd.end)
            _p2m(h, text[cmd.head_pos:eol if eol >= 0 else len(text)], scope)
            continue
        if h == "open":
            body = masked[cmd.head_pos + len(h):cmd.end]
            if not _OPEN_IN.search(masked, cmd.head_pos, cmd.end):
                scope.frames[-1]["opens"] += parse_open(body, scope.ns(), scope.opens())
                continue
        if h in ("variable", "variables"):
            body = masked[cmd.head_pos + len(h):cmd.end]
            scope.frames[-1]["locals"].update(local_names(body, body))
        if h in NOT_USES:
            continue
        ns = scope.ns()
        opens = scope.opens()
        for m in _OPEN_IN.finditer(masked, cmd.start, cmd.head_pos):
            opens = opens + parse_open(m.group(1), ns, opens)
        skip = []
        body_ns = ns
        signature = ""
        if h in DECL_HEADS or h == "example":
            d = decl_name(masked, cmd) if h != "example" else None
            i = cmd.head_pos + len(h)
            if d:
                skip.append((d[1], d[2]))
                i = d[2]
                if not d[0].startswith("_root_."):  # Lean opens a dotted name's namespace
                    body_ns = full_name(ns, d[0]).split(".")[:-1]
            signature = masked[i:signature_end(masked, i, cmd.end)]
        locs = {**scope.locals(), **local_names(masked[cmd.start:cmd.end], signature)}
        for a in _ATTR.finditer(masked, cmd.start, cmd.end):
            skip.append((a.start(), ls._skip_balanced(masked, a.start() + 1, cmd.end)))
        for m in TOKEN.finditer(masked, cmd.start, cmd.end):
            if any(a <= m.start() < b for a, b in skip):
                continue
            g = 1 if m.group(1) else 2 if m.group(2) else 3
            start, end = m.start(g), m.end(g)
            name, cat, field = None, None, True
            if g == 1:
                parts = m.group(1).replace("«", "").replace("»", "").split(".")
                if not any(p in DEF_LAST for p in parts):
                    continue
                a = _AFTER.match(masked, end)
                if a and (a.group(1) == ":=" or len(parts) == 1):
                    continue  # named argument, field, binder or local definition
                if len(parts) == 1 and _in_notation(masked, start, end):
                    continue
                if parts[0] in locs:
                    if len(parts) > 1:
                        name = _field(parts[1], locs[parts[0]], locs, body_ns, opens, rel)
                else:
                    cands, projs = resolve(parts, body_ns, opens, rel)
                    if not cands:  # an undetected local: field notation on it
                        if len(parts) > 1:
                            name = _field(parts[1], None, locs, body_ns, opens, rel)
                    else:
                        targets = {_def_target(c) for c in cands}
                        if len(cands) > 1 and any(targets):
                            diag["ambiguous name"] += 1
                            continue
                        t = targets.pop()
                        if t is None:
                            continue
                        name, cat = t
                        field = False
                        if not cat and projs:
                            # `Def.child` with an unknown child: in a namespace with other
                            # declarations, most likely a generated one (`@[simps]`, `@[ext]`).
                            if name in NAMESPACES:
                                continue
                        elif not cat:
                            cat = classify(masked, start, end)
            else:
                name = _field(m.group(g), None, locs, body_ns, opens, rel)
            if name is None:
                continue
            if field:
                diag["field notation"] += 1
            occ.append((name, _def_file(name), bisect.bisect_right(line_starts, start), cat))
    return rel, occ, diag


def _scan_decls_job(args):
    root, rel = args
    try:
        return scan_decls(Path(root) / rel, rel)
    except (OSError, UnicodeError) as e:
        return {"file": rel, "error": str(e)}


def _scan_uses_job(rel):
    try:
        return scan_uses(rel)
    except (OSError, UnicodeError) as e:
        return rel, [], Counter({f"unreadable file ({type(e).__name__})": 1})


EXCLUDED_DEP_DIRS = {".lake", "test", "tests", "scripts", "docs", "Archive", "Counterexamples",
                     "Lake", "examples", "bench", "Demos", "demos"}


def list_files(root: Path, include: list[str], exclude: list[str]) -> list[str]:
    out = []
    for inc in include or ["."]:
        base = root / inc
        if base.is_file():
            out.append(inc)
            continue
        for p in base.rglob("*.lean"):
            rel = p.relative_to(root).as_posix()
            if not any(fnmatch.fnmatch(rel, g) for g in exclude):
                out.append(rel)
    return sorted(set(out))


def dep_files(root: Path) -> list[str]:
    """Library sources of a dependency: no tests, demos, scripts or loose top-level files."""
    out = []
    for p in root.rglob("*.lean"):
        parts = p.relative_to(root).parts
        dirs = parts[:-1]
        if EXCLUDED_DEP_DIRS & set(dirs) or any(d.endswith(("Test", "Tests")) for d in dirs):
            continue
        if not dirs and not (root / p.stem).is_dir():
            continue
        out.append("/".join(parts))
    return sorted(out)


def build_tables(root: Path, files: list[str], deps: list[Path], jobs: int,
                 diag: Counter, scope: set[str] | None = None) -> dict:
    """Fill the name tables from the project's files and its dependencies; return the
    definitions of the files in `scope` (default: all), {(name, file): {"kind", "line"}}.

    Every project file contributes its names and imports, in scope or not, since Lean
    sees them; only the definitions of the files in scope are counted."""
    global ROOT
    ROOT = root
    for table in (LIB, DUPS, PRIV, DEP, NAMESPACES, DEF_LAST, LIB_LAST, DEP_LAST, IMPORTS):
        table.clear()
    ctx = mp.get_context("fork")
    with ctx.Pool(jobs) as pool:
        lib = pool.map(_scan_decls_job, [(str(root), f) for f in files], chunksize=64)
        dep = []
        for d in deps:
            df = dep_files(d)
            print(f"dependency {d}: {len(df):,} files", file=sys.stderr)
            dep += pool.map(_scan_decls_job, [(str(d), f) for f in df], chunksize=64)
    by_name = defaultdict(list)
    for r in lib:
        if "error" in r:
            diag["unreadable file"] += 1
            continue
        NAMESPACES.update(r["namespaces"])
        for full, kind, line, prot, priv in r["decls"]:
            if priv:
                PRIV.setdefault(r["file"], {})[full] = kind
            else:
                by_name[full].append((kind, r["file"], line, prot))
        for full, kind in r["members"]:
            by_name.setdefault(full, []).append((kind, r["file"], 0, False))
    in_lib = set(files)
    scope = in_lib if scope is None else scope
    for r in lib:
        if "error" not in r:
            IMPORTS[r["file"]] = [f for f in (i.replace(".", "/") + ".lean" for i in r["imports"])
                                  if f in in_lib]
    for name, entries in by_name.items():
        LIB[name] = entries[0]
        files_ = {e[1] for e in entries}
        if len(files_) > 1:
            DUPS[name] = entries
            diag["names declared in several files"] += 1
    for r in dep:
        if "error" in r:
            continue
        NAMESPACES.update(r["namespaces"])
        for full, kind, line, prot, priv in r["decls"]:
            if not priv:
                DEP[full] = prot
        for full, kind in r["members"]:
            DEP.setdefault(full, False)
    for name in list(LIB) + list(DEP):
        parts = name.split(".")
        for i in range(1, len(parts)):
            NAMESPACES.add(".".join(parts[:i]))
    for name, info in LIB.items():
        last = name.rsplit(".", 1)[-1]
        LIB_LAST.setdefault(last, []).append(name)
        if info[0] in DEF_KINDS:
            DEF_LAST.add(last)
    DEP_LAST.update(n.rsplit(".", 1)[-1] for n in DEP)
    defs = {}
    for name, entries in by_name.items():
        for kind, file, line, _ in entries:
            if kind in DEF_KINDS and file in scope:
                defs[name, file] = {"kind": kind, "line": line}
    print(f"library names: {len(LIB):,}, definitions: {len(defs):,}, "
          f"dependency names: {len(DEP):,}", file=sys.stderr)
    return defs


def run_source(root: Path, include: list[str], exclude: list[str], deps: list[Path],
               jobs: int, label: str = "", uses: list | None = None, commands=()):
    """Source backend. `include`/`exclude` select the files whose definitions and uses are
    counted; all `.lean` files under `root` provide names and imports. `commands` are
    command keywords the library defines (FLT's `p2m_*` scoping commands are understood)."""
    EXTRA_COMMANDS.clear()
    EXTRA_COMMANDS.update(commands)
    files = list_files(root, include, exclude)
    project = list_files(root, [], ["*/.lake/*", ".lake/*"])
    print(f"library files: {len(files):,} in scope, {len(project):,} in the project",
          file=sys.stderr)
    diag = Counter()
    defs = build_tables(root, project, deps, jobs, diag, set(files))
    ctx = mp.get_context("fork")
    gc.collect()
    gc.freeze()  # keep the shared tables out of the workers' garbage collection

    def occurrences():
        with ctx.Pool(jobs) as pool:
            for i, (rel, occ, d) in enumerate(pool.imap_unordered(_scan_uses_job, files,
                                                                   chunksize=32)):
                diag.update(d)
                for n, df, line, cat in occ:
                    yield n, df, rel, line, cat
                if (i + 1) % 20000 == 0:
                    print(f"  uses: {i + 1:,}/{len(files):,} files", file=sys.stderr)
    rows, unfoldings = aggregate(defs, occurrences(), uses)
    gc.unfreeze()
    meta = {"backend": "source", "label": label, "root": display_path(root),
            "commit": git_commit(root), "include": include, "exclude": exclude,
            "deps": [display_path(d) for d in deps],
            "dep_commits": {display_path(d): git_commit(d) for d in deps},
            "commands": sorted(commands),
            "files": len(files), "project_files": len(project), "diagnostics": dict(diag)}
    return meta, rows, unfoldings


# ---------------------------------------------------------------------------------------
# Comparison of two outputs (normally ilean reference vs source)

def _load(d: Path):
    meta = json.loads((d / "meta.json").read_text())
    rows = [json.loads(l) for l in open(d / "defs.jsonl")]
    unf = [json.loads(l) for l in open(d / "unfoldings.jsonl")]
    return meta, rows, unf


def _spearman(xs, ys) -> float:
    def ranks(v):
        order = sorted(range(len(v)), key=lambda i: v[i])
        r = [0.0] * len(v)
        i = 0
        while i < len(order):
            j = i
            while j + 1 < len(order) and v[order[j + 1]] == v[order[i]]:
                j += 1
            for k in range(i, j + 1):
                r[order[k]] = (i + j) / 2
            i = j + 1
        return r
    rx, ry = ranks(xs), ranks(ys)
    n = len(xs)
    mx, my = sum(rx) / n, sum(ry) / n
    cov = sum((a - mx) * (b - my) for a, b in zip(rx, ry))
    vx = sum((a - mx) ** 2 for a in rx) ** .5
    vy = sum((b - my) ** 2 for b in ry) ** .5
    return cov / (vx * vy) if vx and vy else float("nan")


def compare(ref_dir: Path, other_dir: Path, samples: int = 15) -> str:
    rmeta, rrows, runf = _load(ref_dir)
    ometa, orows, ounf = _load(other_dir)
    stale = set(rmeta.get("stale_files", [])) | set(ometa.get("stale_files", []))
    R = {(r["name"], r["file"]): r for r in rrows if r["file"] not in stale}
    O = {(r["name"], r["file"]): r for r in orows if r["file"] not in stale}
    common = R.keys() & O.keys()
    out = [f"# Source backend against the ilean reference: {rmeta.get('label', '')}".rstrip(),
           "", f"Reference: `{ref_dir}` ({rmeta['backend']}). Compared: `{other_dir}` "
           f"({ometa['backend']}).", ""]
    if stale:
        out += [f"{len(stale):,} files whose build index does not match the source are left "
                "out on both sides.", ""]
    out += ["## Definitions", "",
            f"- found by both: {len(common):,}",
            f"- only in the reference: {len(R.keys() - O.keys()):,}",
            f"- only in the compared output: {len(O.keys() - R.keys()):,}", ""]
    for title, keys in (("Only in the reference", R.keys() - O.keys()),
                        ("Only in the compared output", O.keys() - R.keys())):
        ks = sorted(keys)[:samples]
        if ks:
            out += [f"{title} (first {len(ks)}): " + ", ".join(f"`{n}`" for n, _ in ks), ""]

    def keyed(unf):
        return Counter((u["def"], u["def_file"], u["file"], u["line"], u["category"])
                       for u in unf if (u["def"], u["def_file"]) in common
                       and u["file"] not in stale)
    rk, ok = keyed(runf), keyed(ounf)
    out += ["## Explicit unfoldings (definitions found by both)", "",
            "| Category | Scope | Reference | Compared | Matched | Precision | Recall |",
            "|---|---|---:|---:|---:|---:|---:|"]
    for cat in CATEGORIES + ("all",):
        for scope_name, scopes in (("all", SCOPES), ("outside file", ("dir", "outside")),
                                   ("outside directory", ("outside",))):
            def sel(c):
                return Counter({k: v for k, v in c.items()
                                if (cat == "all" or k[4] == cat)
                                and scope_of(k[1], k[2]) in scopes})
            a, b = sel(rk), sel(ok)
            tp = sum((a & b).values())
            na, nb = sum(a.values()), sum(b.values())
            out.append(f"| {cat} | {scope_name} | {na:,} | {nb:,} | {tp:,} | "
                       f"{_pct(tp, nb)} | {_pct(tp, na)} |")
    out.append("")
    for title, diff in (("Missed (in the reference only)", rk - ok),
                        ("Spurious (in the compared output only)", ok - rk)):
        items = sorted(diff.elements())[:samples]
        if items:
            out += [f"{title}, first {len(items)}:", ""]
            out += [f"- `{d}` at `{f}:{l}` ({c})" for d, _, f, l, c in items]
            out.append("")
    out += ["## Uses (definitions found by both)", "",
            "| Scope | Reference uses | Compared uses | Ratio | Spearman per definition |",
            "|---|---:|---:|---:|---:|"]
    keys = sorted(common)
    for scope_name, scopes in (("all", SCOPES), ("outside file", ("dir", "outside")),
                               ("outside directory", ("outside",))):
        xs = [sum(R[k]["uses"][s] for s in scopes) for k in keys]
        ys = [sum(O[k]["uses"][s] for s in scopes) for k in keys]
        sx, sy = sum(xs), sum(ys)
        out.append(f"| {scope_name} | {sx:,} | {sy:,} | {sy / sx:.3f} | "
                   f"{_spearman(xs, ys):.3f} |" if sx else
                   f"| {scope_name} | 0 | {sy:,} | – | – |")
    out.append("")
    if (ref_dir / "uses.jsonl").exists() and (other_dir / "uses.jsonl").exists():
        def use_keys(d):
            return Counter(tuple(u) for u in map(json.loads, open(d / "uses.jsonl"))
                           if (u[0], u[1]) in common and u[2] not in stale)
        ru, ou = use_keys(ref_dir), use_keys(other_dir)
        out += ["Individual uses, matched by definition, file and line:", "",
                "| Scope | Reference | Compared | Matched | Precision | Recall |",
                "|---|---:|---:|---:|---:|---:|"]
        for scope_name, scopes in (("all", SCOPES), ("outside file", ("dir", "outside")),
                                   ("outside directory", ("outside",))):
            a = Counter({k: v for k, v in ru.items() if scope_of(k[1], k[2]) in scopes})
            b = Counter({k: v for k, v in ou.items() if scope_of(k[1], k[2]) in scopes})
            tp = sum((a & b).values())
            na, nb = sum(a.values()), sum(b.values())
            out.append(f"| {scope_name} | {na:,} | {nb:,} | {tp:,} | {_pct(tp, nb)} | "
                       f"{_pct(tp, na)} |")
        out.append("")
        spurious = sorted((ou - ru).elements())
        if spurious:
            step = max(1, len(spurious) // samples)
            out += [f"Uses in the compared output only (every {step}th of {len(spurious):,}):",
                    ""]
            out += [f"- `{d}` at `{f}:{l}`" for d, _, f, l in spurious[::step][:samples]]
            out.append("")
    worst = sorted(keys, key=lambda k: -abs(sum(R[k]["uses"].values())
                                            - sum(O[k]["uses"].values())))[:samples]
    out += ["Largest differences in total uses:", "",
            "| Definition | Reference | Compared |", "|---|---:|---:|"]
    out += [f"| `{k[0]}` | {sum(R[k]['uses'].values())} | {sum(O[k]['uses'].values())} |"
            for k in worst]
    out.append("")
    rs, os_ = summarize([R[k] for k in keys]), summarize([O[k] for k in keys])
    out += ["## Library indicators (definitions found by both)", "",
            "| Group | Where | Measure | Reference | Compared |", "|---|---|---|---:|---:|"]
    for group in GROUPS:
        for label in ("outside_file", "outside_dir"):
            a, b = rs[group][label], os_[group][label]
            for meas, fa, fb in (
                    ("definitions used", a["used"], b["used"]),
                    ("definitions unfolded", a["unfolded"], b["unfolded"]),
                    ("share unfolded", _pct(a["unfolded"], a["used"]),
                     _pct(b["unfolded"], b["used"])),
                    ("unfoldings", a["total_unfoldings"], b["total_unfoldings"]),
                    ("unfoldings per 100 uses",
                     f"{100 * a['total_unfoldings'] / a['uses']:.2f}" if a["uses"] else "–",
                     f"{100 * b['total_unfoldings'] / b['uses']:.2f}" if b["uses"] else "–")):
                out.append(f"| {group} | {label.replace('_', ' ')} | {meas} | {fa} | {fb} |")
    out.append("")
    return "\n".join(out)


# ---------------------------------------------------------------------------------------

def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    sub = ap.add_subparsers(dest="cmd", required=True)
    s = sub.add_parser("source", help="source-only backend")
    s.add_argument("--root", type=Path, required=True)
    s.add_argument("--include", nargs="*", default=[], help="directories under the root")
    s.add_argument("--exclude", action="append", default=[], help="glob on relative paths")
    s.add_argument("--deps", type=Path, nargs="*", action="extend", default=[],
                   help="source roots of the dependencies (for name resolution)")
    s.add_argument("--jobs", type=int, default=max(1, (mp.cpu_count() or 2) - 2))
    s.add_argument("--label", default="")
    s.add_argument("--save-uses", action="store_true", help="also write every use (uses.jsonl)")
    s.add_argument("--command", action="append", default=[],
                   help="a command keyword the library defines (e.g. p2m_open)")
    s.add_argument("--out", type=Path, required=True)
    i = sub.add_parser("ilean", help="reference backend, needs a built library")
    i.add_argument("--root", type=Path, required=True)
    i.add_argument("--lib", nargs="+", required=True, help="module prefixes, e.g. Mathlib")
    i.add_argument("--jobs", type=int, default=max(1, (mp.cpu_count() or 2) - 2))
    i.add_argument("--label", default="")
    i.add_argument("--save-uses", action="store_true", help="also write every use (uses.jsonl)")
    i.add_argument("--out", type=Path, required=True)
    c = sub.add_parser("compare", help="compare an output with a reference output")
    c.add_argument("ref", type=Path)
    c.add_argument("other", type=Path)
    c.add_argument("--out", type=Path, help="write the comparison here (markdown)")
    a = ap.parse_args(argv)
    if a.cmd == "compare":
        text = compare(a.ref, a.other)
        if a.out:
            a.out.write_text(text)
        print(text)
        return
    uses = [] if a.save_uses else None
    if a.cmd == "source":
        meta, rows, unf = run_source(a.root.resolve(), a.include, a.exclude,
                                     [d.resolve() for d in a.deps], a.jobs, a.label, uses,
                                     a.command)
    else:
        import def_unfolds_ilean
        meta, rows, unf = def_unfolds_ilean.run(a.root.resolve(), a.lib, a.jobs, a.label,
                                                uses)
    summary = write_output(a.out, meta, rows, unf, uses)
    for group, g in summary.items():
        f, d = g["outside_file"], g["outside_dir"]
        print(f"{group}: {g['definitions']:,} definitions; unfolded outside their file: "
              f"{f['unfolded']:,}/{f['used']:,} used there ({f['total_unfoldings']:,} "
              f"unfoldings); outside their directory: {d['unfolded']:,}/{d['used']:,} "
              f"({d['total_unfoldings']:,})")


if __name__ == "__main__":
    main()
