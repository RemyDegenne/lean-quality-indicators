# Explicit unfoldings of definitions outside their file (2026-11-02)

For each public `def`/`abbrev` (and named `instance`), [def_unfolds.py](../../scripts/def_unfolds.py)
counts its uses and its explicit unfoldings (`unfold`/`delta`/`unseal`, a bare item of a
`simp`-like or `rw`-like list, an equation lemma `foo.eq_def`) in its own file, in the rest
of its directory (subdirectories included) and elsewhere. Every definition is counted, no
sampling and no LLM. Commands are in
[RUNNING.md](../../RUNNING.md#explicit-unfoldings-of-definitions).

## Results

[library-comparison.md](library-comparison.md) has the full table (scope, categories).
`def`/`abbrev` only:

| Library | Definitions | Unfolded outside file / used there | Per 100 uses | Unfolded outside directory / used there | Per 100 uses |
|---|---:|---:|---:|---:|---:|
| Mathlib | 34,098 | 2,858 / 15,006 (19.0%) | 2.92 | 1,686 / 10,234 (16.5%) | 2.54 |
| Tau Ceti | 23,273 | 308 / 14,775 (2.1%) | 0.31 | 118 / 8,504 (1.4%) | 0.27 |
| Lean Pool | 74,932 | 16,390 / 38,513 (42.6%) | 5.32 | 3,071 / 8,790 (34.9%) | 4.48 |
| FLT (Anthropic) | 78,206 | 2,425 / 6,683 (36.3%) | 2.00 | 2,390 / 6,460 (37.0%) | 1.99 |
| Formal Frontier | 3,821 | 133 / 1,416 (9.4%) | 1.54 | 12 / 199 (6.0%) | 1.14 |
| OpenAI Math | 1,117,060 | 145,562 / 322,130 (45.2%) | 6.37 | 32,351 / 109,261 (29.6%) | 6.01 |
| CFSG (AxiomMath) | 275,245 | 40,449 / 168,869 (24.0%) | 2.42 | 10,348 / 49,991 (20.7%) | 1.99 |

One directory per library (`mathlib/`, `tauceti/`, `lean-pool/`, `flt-anthropic/`,
`formal-frontier/`, `openai-math/`, `axiom-cfsg/`), each with `report.md` (counts by scope
and category, most unfolded definitions), `summary.json` and `meta.json` (commits,
dependencies, diagnostics). The per-definition data, `defs.jsonl` (every definition) and
`unfoldings.jsonl` (every explicit unfolding, with file and line), is not versioned
(1.4 GB): `python3 scripts/def_unfolds_corpus.py` regenerates it from the pinned sources. The corpus is pinned as in the other audits; names are
resolved against every package of each library's `lake-manifest.json` and the Lean core of
its exact toolchain.

Reading notes:

- The directory scope depends on each library's layout. FLT keeps its 29,511 solution
  files in one directory (`P2M/Sol/`), and its definitions in `Definitions/`, so almost all
  of its uses outside a file are also outside the directory.
- Formal Frontier is measured repository by repository: a definition used from another of
  its repositories counts there as a dependency, not as a use.
- FLT's scoping commands `p2m_open`, `p2m_export` and `p2m_alias` are interpreted.

## Validation of the source backend

`validation/` compares the source backend with the ilean backend, which reads the names
Lean resolved in a build (`.ilean` files), on the local Mathlib checkout (`e5f8f2f`) and
LMLPapers. Modules whose build no longer matches the source are left out (7 in Mathlib,
23 in LMLPapers).

Explicit unfoldings outside the defining file:

| Library | Reference | Source | Precision | Recall |
|---|---:|---:|---:|---:|
| Mathlib | 10,811 | 10,819 | 99.4% | 99.4% |
| LMLPapers | 158 | 158 | 100.0% | 100.0% |

Uses outside the defining file, matched by definition, file and line:

| Library | Reference | Source | Precision | Recall |
|---|---:|---:|---:|---:|
| Mathlib | 478,888 | 378,192 | 97.8% | 77.2% |
| LMLPapers | 8,233 | 7,673 | 100.0% | 93.2% |

Missed uses are mostly field notation on expressions (`(f x).natDegree`), which needs type
inference, and names that two opened namespaces make ambiguous. So the counts of
definitions unfolded are accurate, while the counts of definitions used and of uses are
lower bounds: shares and rates per use are slightly high, most for Mathlib, whose common
names (`symm`, `map`, `trans`) exist in many namespaces.
