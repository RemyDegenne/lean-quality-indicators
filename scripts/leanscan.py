"""Lightweight Lean 4 source scanner.

Splits a Lean file into top-level commands, tracks the namespace/section scopes, and
reconstructs, for each `theorem`/`lemma`, the context it is elaborated in: the enclosing
`namespace`/`section` openers and the `variable`, `open`, `universe`, `include`, `omit`,
`set_option`, local attribute, local instance and notation commands still in effect.

The scanner is syntactic and assumes the usual Lean/Mathlib layout, where top-level
commands start at column 0. It does not need the library to be built.
"""

from __future__ import annotations

import bisect
import re
from dataclasses import dataclass, field

MODIFIERS = {
    "private", "protected", "noncomputable", "nonrec", "partial", "unsafe", "public",
    "meta", "scoped", "local",
}
THEOREM_KW = {"theorem", "lemma"}
DECL_KW = THEOREM_KW | {
    "def", "abbrev", "instance", "structure", "class", "inductive", "coinductive",
    "example", "axiom", "opaque", "irreducible_def", "alias", "builtin_initialize",
    "initialize", "deriving", "add_decl_doc", "unif_hint", "simproc", "simproc_decl",
    "dsimproc", "dsimproc_decl", "grind_pattern", "proof_wanted", "doc_alias",
}
SCOPE_KW = {"namespace", "section", "end", "mutual"}
NOTATION_KW = {
    "notation", "notation3", "infix", "infixl", "infixr", "prefix", "postfix",
    "macro", "macro_rules", "syntax", "elab", "elab_rules", "binder_predicate",
}
# Commands that stay in effect until the enclosing scope closes.
CONTEXT_KW = {
    "variable", "variables", "open", "universe", "universes", "include", "omit",
    "set_option", "attribute", "export",
} | NOTATION_KW
# Commands that can prefix another command with `... in`.
IN_PREFIX_KW = {"open", "variable", "include", "omit", "set_option", "attribute"}
OTHER_KW = {
    "import", "module", "assert_not_exists", "assert_not_imported", "library_note",
    "suppress_compilation", "unseal", "seal", "compile_inductive", "run_cmd", "run_elab",
    "run_meta", "declare_syntax_cat", "register_option", "register_simp_attr",
    "register_label_attr", "declare_config_elab", "initialize_simps_projections",
    "mk_iff_of_inductive_prop", "count_heartbeats", "recall", "extend_docs",
    "deprecated_module", "recommended_spelling", "to_dual_for", "to_dual_name_hint",
    "to_dual_insert_cast", "to_dual_insert_cast_fun", "insert_to_additive_translation",
    "insert_to_dual_translation", "declare_aesop_rule_sets", "add_aesop_rules",
    "register_linter_set", "name_poly_vars", "name_power_vars", "unsuppress_compilation",
    "tactic_extension", "assert_no_sorry", "assert_only_standard_axioms",
    "real_normed_space_shortcut_instances",
}

_WORD_RE = re.compile(r"#?[A-Za-z_][A-Za-z0-9_!?']*")
_NAME_RE = re.compile(r"(?:«[^»]*»|[^\s()\[\]{}:,⦃⦄«»])+")
_IN_RE = re.compile(r"(?<![\w.'])in(?![\w'!?])")
_SPECIAL_RE = re.compile(r'/-|--|"')
_BLOCK_RE = re.compile(r"/-|-/")
_NOT_NL = re.compile(r"[^\n]")


@dataclass
class Command:
    start: int          # offset of the first character (docstring included)
    end: int            # offset just after the last significant character
    head: str           # head keyword after docstring, attributes, modifiers, `... in`
    head_pos: int       # offset of the head keyword
    mods: list[str]     # modifiers before the head keyword
    attrs: str          # attribute prefixes (masked text)
    line: int           # 1-based line of `start`


@dataclass
class Frame:
    opener_text: str | None      # None for the file frame and for `mutual`
    names: list[str]
    kind: str                    # "file", "namespace", "section", "mutual"
    ctx: list[Command] = field(default_factory=list)


@dataclass
class Theorem:
    cmd: Command
    name: str
    full_name: str
    deprecated: bool
    end_line: int
    frames: list[tuple[str | None, str, list[Command]]]  # (opener_text, kind, ctx)


def mask(text: str) -> tuple[str, list[tuple[int, int]]]:
    """Blank out comments and string literals (newlines kept, offsets preserved).

    Returns the masked text and the spans of doc comments (`/-- ... -/`)."""
    spans: list[tuple[int, int]] = []
    docs: list[tuple[int, int]] = []
    n = len(text)
    i = 0
    while True:
        m = _SPECIAL_RE.search(text, i)
        if not m:
            break
        s = m.start()
        tok = m.group()
        if tok == "--":
            e = text.find("\n", s)
            e = n if e == -1 else e
        elif tok == "/-":
            depth, j = 1, s + 2
            while depth:
                b = _BLOCK_RE.search(text, j)
                if not b:
                    j = n
                    break
                depth += 1 if b.group() == "/-" else -1
                j = b.end()
            e = j
            if text.startswith("/--", s) and not text.startswith("/--/", s):
                docs.append((s, e))
        else:  # string literal, unless it is the char literal '"'
            if 0 < s and text[s - 1] == "'" and text[s + 1:s + 2] == "'":
                i = s + 2
                continue
            j = s + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            e = min(j + 1, n)
        spans.append((s, e))
        i = e
    pieces = []
    prev = 0
    for s, e in spans:
        pieces.append(text[prev:s])
        pieces.append(_NOT_NL.sub(" ", text[s:e]))
        prev = e
    pieces.append(text[prev:])
    return "".join(pieces), docs


def _skip_balanced(masked: str, i: int, end: int) -> int:
    depth = 0
    while i < end:
        c = masked[i]
        if c == "[":
            depth += 1
        elif c == "]":
            depth -= 1
            if depth == 0:
                return i + 1
        i += 1
    return end


def parse_head(masked: str, i: int, end: int):
    """Skip docstring/attribute/modifier prefixes from offset `i`.

    Returns (head_word or "", head_pos, modifiers, attrs_text)."""
    mods: list[str] = []
    attrs: list[str] = []
    while True:
        while i < end and masked[i].isspace():
            i += 1
        if i >= end:
            return "", i, mods, " ".join(attrs)
        if masked.startswith("@[", i):
            j = _skip_balanced(masked, i + 1, end)
            attrs.append(masked[i:j])
            i = j
            continue
        m = _WORD_RE.match(masked, i)
        if not m:
            return "", i, mods, " ".join(attrs)
        w = m.group()
        if w in MODIFIERS:
            mods.append(w)
            i = m.end()
            if w == "scoped" and masked.startswith("[", i):  # scoped[NS] notation
                i = _skip_balanced(masked, i, end)
            continue
        return w, i, mods, " ".join(attrs)


def _is_start_word(w: str, extra: set[str]) -> bool:
    return (w in DECL_KW or w in SCOPE_KW or w in CONTEXT_KW or w in OTHER_KW
            or w in MODIFIERS or w in extra or (w.startswith("#") and len(w) > 1))


def split_commands(masked: str, docs: list[tuple[int, int]],
                   extra_cmds: set[str] = frozenset()) -> list[Command]:
    """Split a file into top-level commands (column-0 heuristic).

    Docstrings, attribute lines and `open Foo in`-style lines are merged into the command
    that follows them."""
    doc_starts = {s for s, _ in docs}
    line_starts = [0] + [m.end() for m in re.finditer("\n", masked)]
    starts: list[int] = []
    for ls in line_starts:
        if ls >= len(masked):
            continue
        c = masked[ls]
        if ls in doc_starts or masked.startswith("@[", ls):
            starts.append(ls)
        elif not c.isspace():
            m = _WORD_RE.match(masked, ls)
            if m and _is_start_word(m.group(), extra_cmds):
                starts.append(ls)
    cmds: list[Command] = []
    pending: int | None = None   # start of the prefix lines merged into the next command
    p_mods: list[str] = []
    p_attrs: list[str] = []
    for idx, s in enumerate(starts):
        e = starts[idx + 1] if idx + 1 < len(starts) else len(masked)
        real_end = s + len(masked[s:e].rstrip())
        head, hpos, mods, attrs = parse_head(masked, s, real_end)
        while head in IN_PREFIX_KW:
            m = _IN_RE.search(masked, hpos + len(head), real_end)
            if not m:
                break
            h2, p2, mods2, attrs2 = parse_head(masked, m.end(), real_end)
            head, hpos = h2, p2
            mods, attrs = mods + mods2, f"{attrs} {attrs2}"
        if not head:  # prefix only: docstring, attributes, modifiers, `open Foo in`
            if pending is None:
                pending = s
            p_mods += mods
            p_attrs.append(attrs)
            continue
        cs = s if pending is None else pending
        cmds.append(Command(start=cs, end=real_end, head=head, head_pos=hpos,
                            mods=p_mods + mods, attrs=" ".join(p_attrs + [attrs]),
                            line=bisect.bisect_right(line_starts, cs)))
        pending, p_mods, p_attrs = None, [], []
    return cmds


def strip_docs(text: str, start: int, end: int, docs: list[tuple[int, int]]) -> str:
    """Original text of [start, end) with doc comments removed."""
    pieces = []
    i = start
    for ds, de in docs:
        if de <= start or ds >= end:
            continue
        pieces.append(text[i:ds])
        i = de
        if (ds == 0 or text[ds - 1] == "\n") and text[de:de + 1] == "\n":
            i += 1  # the doc comment filled its lines: drop the line break too
    pieces.append(text[i:end])
    out = "".join(pieces)
    out = re.sub(r"\n[ \t]*(?=\n)", "\n", out)   # lines emptied by the removal
    return re.sub(r"\n{3,}", "\n\n", out).strip("\n")


def _first_word_after(masked: str, cmd: Command) -> str:
    rest = masked[cmd.head_pos + len(cmd.head):cmd.end].split()
    return rest[0] if rest else ""


def _attr_kinds(masked: str, cmd: Command) -> str:
    m = re.match(r"attribute\s*\[([^\]]*)\]", masked[cmd.head_pos:cmd.end])
    return m.group(1) if m else ""


def _dropped_at_scope_end(masked: str, cmd: Command) -> bool:
    if cmd.head in NOTATION_KW:
        return "local" in cmd.mods or "scoped" in cmd.mods
    if cmd.head == "attribute":
        return bool(re.search(r"\b(local|scoped)\b", _attr_kinds(masked, cmd)))
    return True


def scan(text: str, extra_ctx: set[str] = frozenset(), extra_other: set[str] = frozenset(),
         with_context: bool = True):
    """Return (theorems, docs) for one file."""
    masked, docs = mask(text)
    cmds = split_commands(masked, docs, set(extra_ctx) | set(extra_other))
    line_starts = [0] + [m.end() for m in re.finditer("\n", masked)]
    frames: list[Frame] = [Frame(None, [], "file")]
    theorems: list[Theorem] = []

    def ns_prefix() -> str:
        return ".".join(n for f in frames if f.kind == "namespace" for n in f.names)

    def pop_frame():
        f = frames.pop()
        # Global notations and global attributes outlive the scope.
        frames[-1].ctx.extend(c for c in f.ctx if not _dropped_at_scope_end(masked, c))

    for cmd in cmds:
        h = cmd.head
        if h in ("namespace", "section"):
            name = _first_word_after(masked, cmd)
            names = [p for p in name.replace("«", "").replace("»", "").split(".") if p]
            frames.append(Frame(strip_docs(text, cmd.start, cmd.end, docs), names, h))
        elif h == "mutual":
            frames.append(Frame(None, [], "mutual"))
        elif h == "end":
            if len(frames) == 1:
                continue
            name = _first_word_after(masked, cmd)
            remaining = [p for p in name.split(".") if p]
            if not remaining:
                pop_frame()
                continue
            while remaining and len(frames) > 1:
                f = frames[-1]
                k = len(f.names)
                if k and k <= len(remaining) and f.names == remaining[-k:]:
                    remaining = remaining[:-k]
                    pop_frame()
                elif k and len(remaining) < k and f.names[-len(remaining):] == remaining:
                    # `namespace A.B` closed by `end B`: `namespace A` stays open.
                    f.names = f.names[:-len(remaining)]
                    f.opener_text = f"{f.kind} {'.'.join(f.names)}"
                    remaining = []
                else:  # malformed nesting: close one scope and move on
                    pop_frame()
                    remaining = []
        elif h in CONTEXT_KW or h in extra_ctx:
            if h == "attribute" and not re.search(r"\b(local|scoped|instance)\b",
                                                  _attr_kinds(masked, cmd)):
                continue
            frames[-1].ctx.append(cmd)
        elif h == "instance" and ("local" in cmd.mods or "scoped" in cmd.mods):
            frames[-1].ctx.append(cmd)
        elif h in THEOREM_KW:
            name = _first_word_after(masked, cmd)
            m = _NAME_RE.match(name)
            name = m.group() if m else "?"
            if name.startswith("_root_."):
                full = name[len("_root_."):]
            else:
                p = ns_prefix()
                full = f"{p}.{name}" if p else name
            snap = [(f.opener_text, f.kind, list(f.ctx)) for f in frames] if with_context else []
            theorems.append(Theorem(cmd=cmd, name=name, full_name=full,
                                    deprecated="deprecated" in cmd.attrs,
                                    end_line=bisect.bisect_right(line_starts, cmd.end - 1),
                                    frames=snap))
    return theorems, docs


def render_context(text: str, docs, thm: Theorem) -> str:
    """Self-contained snippet: scope openers, context commands, the theorem, `end`s."""
    out: list[str] = []
    closers: list[str] = []
    for opener_text, kind, ctx in thm.frames:
        if opener_text is not None:
            out += [opener_text, ""]
            words = opener_text.split()
            i = words.index(kind) if kind in words else -1
            name = words[i + 1] if 0 <= i < len(words) - 1 else ""
            closers.append(f"end {name}".rstrip())
        for c in ctx:
            out += [strip_docs(text, c.start, c.end, docs), ""]
    out += [strip_docs(text, thm.cmd.start, thm.cmd.end, docs), ""]
    out += reversed(closers)
    return "\n".join(out).rstrip() + "\n"
