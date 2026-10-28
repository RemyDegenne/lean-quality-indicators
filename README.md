# Quality indicators for Lean libraries

This repository measures the quality of Lean 4 mathematics libraries, most of them
written largely by AI agents, and compares them with Mathlib. Each *indicator* (or
*audit*) asks an LLM judge one precise question about a sampled theorem, definition or
file, for example "can a hypothesis of this theorem be deleted?". The judge reads the
sources but cannot run Lean. For each library we report the share of sampled targets
the judge flags, with a 95% confidence interval.

The indicators are local measures of formalization quality: unnecessary assumptions,
results already in Mathlib, definitions that miss their intended object, repeated
reasoning, and similar. They say nothing about the importance, difficulty or coverage of
a formalization.

## Where the results are

| File | Content |
|---|---|
| [Whitepaper](reports/formalization-quality-whitepaper.md) ([PDF](reports/formalization-quality-whitepaper.pdf)) | Two-page summary of the main findings |
| [AUDIT_RESULTS.md](AUDIT_RESULTS.md) ([JSON](AUDIT_RESULTS.json)) | Every main audit, for every library and judge: coverage, flag rates, correlations between judges, costs |
| [AUDIT_METHODS.md](AUDIT_METHODS.md) | Notation and aggregation rules of the reports |
| [AUDIT_APPENDIX.md](AUDIT_APPENDIX.md) | Two file audits that are not reliable enough yet for library comparisons |
| [Costs](runs/main/api-equivalent-costs.md) | API-equivalent cost of each audit and judge |
| `runs/<run>/<indicator>/<label>/report.md` | One judge run: rates per library and every flag, with the judge's argument and a link to the source |

Comparisons of all judges on one audit:
[unnecessary hypotheses](runs/main/unnecessary-hypotheses/audit-comparison.md),
[duplicates of Mathlib](runs/main/duplicates-mathlib-inclusive/audit-comparison.md),
[definition fidelity](runs/defs1/definition-fidelity/audit-comparison.md), and each file
audit in [`runs/file-quality-pilot-2026-10-21/reports/`](runs/file-quality-pilot-2026-10-21/reports/)
(`<audit>-comparison.md`). The later runs have their own pages:
OpenAI Math ([theorems](runs/openai-math-2026-10-21/scale-300/theorems/library-comparison.md)),
CFSG ([files](runs/cfsg-pilot-2026-10-27/library-comparison.md),
[theorems](runs/cfsg-pilot-2026-10-27/theorems/library-comparison.md),
[300-target expansion](runs/cfsg-pilot-2026-10-27/scale-300/progress.md)) and the
[file-audit expansion](runs/library-quality-scale-2026-10-26/library-comparison.md).

## Sources evaluated

| Library | Repository | Scope | Commit | Eligible theorems | Eligible definitions |
|---|---|---|---|---:|---:|
| Mathlib | [leanprover-community/mathlib4](https://github.com/leanprover-community/mathlib4) | `Mathlib/` without `Tactic`, `Util`, `Lean`, `Testing`, `Deprecated` | `e3e75e8` (2026-10-19) | 187,171 | 37,545 |
| Tau Ceti | [TauCetiProject/TauCeti](https://github.com/TauCetiProject/TauCeti) | `TauCeti/` | `e8b7b60` (2026-10-19) | 135,838 | 23,974 |
| Lean Pool | [Vilin97/lean-pool](https://github.com/Vilin97/lean-pool) | `LeanPool/` | `01db1d7` (2026-10-07) | 233,671 | 78,295 |
| FLT (Anthropic) | [anthropics/fermats-last-theorem](https://github.com/anthropics/fermats-last-theorem) | `P2M/Sol`, `P2M/Derive`, `Definitions` | `6e837e7` (2026-09-24) | 433,929 | 79,590 |
| Formal Frontier | the 43 libraries of [FormalFrontier](https://github.com/FormalFrontier) | the main `lean_lib` of each repository | one per repository | 10,318 | 3,884 |
| OpenAI Math | [openai/math](https://github.com/openai/math) | `lean/OAI/` | `1581d4c` | 1,433,851 | — |
| CFSG (AxiomMath) | [AxiomMath/CFSG](https://github.com/AxiomMath/CFSG) | `CFSG/` | `5f8042b` | 1,363,165 | — |

The first five libraries (47 repositories) are defined in [libraries.toml](libraries.toml)
and pinned in [libraries.lock.json](libraries.lock.json). OpenAI Math and CFSG were added
later as separate corpora, pinned in
[runs/openai-math-2026-10-21/libraries.lock.json](runs/openai-math-2026-10-21/libraries.lock.json)
and [runs/cfsg-pilot-2026-10-27/corpus-lock.json](runs/cfsg-pilot-2026-10-27/corpus-lock.json).
The judges can also read the dependencies each library pins (Mathlib, Batteries, and for
CFSG Tau Ceti and others) and Lean core.

Scope decisions, applied everywhere unless stated:

- **Eligible declarations** are the `theorem`s and `lemma`s of the included files (for
  definitions: `def`, `abbrev`, `structure`, `class`, `irreducible_def`). Deprecated
  declarations are skipped as compatibility shims, and `private` ones because private
  helpers often carry normalising hypotheses set up by their caller.
- **`*/Certificates/*` is excluded**: machine-generated numerical checks (about 81K in Lean
  Pool, which would otherwise be 22% of its sample).
- **FLT**: the `Theorems/Thm_*.lean` wrappers are skipped, since each restates a `solution`
  theorem of `P2M/Sol` and delegates its proof to it. About 93% of the population are
  helper lemmas of the `P2M/Sol` proofs.
- **Formal Frontier**: not the `pod` agent manager, the Sutherland drafts or the
  Test/Examples libraries.
- **CFSG**: the full tree has 229,089 Lean files, of which 194,203 are candidates under
  `CFSG/` once certificate directories are excluded
  ([census](runs/cfsg-pilot-2026-10-27/source-census.json)).

## What is measured

### Theorem indicators

One sampled theorem at a time ([`indicators/`](indicators/): prompt, message, answer
schema and settings of each).

- **`unnecessary-hypotheses`**: a hypothesis of the theorem (one of its binders, or one it
  takes from a `variable` command) can be deleted, leaving a statement that is still true
  and provable, possibly with a different proof. This includes redundant typeclass
  instances. Weakening a hypothesis does not count.
- **`duplicates-mathlib`**: the theorem is already in Mathlib (with Batteries and Lean
  core), either as the same statement up to presentation (`duplicate`) or as an
  instantiation of a single Mathlib declaration provable from it in one or two short lines
  (`special_case`). General principles of logic, equality and structure (`Eq.subst`,
  `map_add`, ext lemmas, …) applied to the library's own definitions do not count. Judged
  against the Mathlib version each library pins. This first version was not run on
  Mathlib itself.
- **`duplicates-mathlib-inclusive`**: the same criteria, also applied to Mathlib. A match
  must be a distinct declaration: the target itself, its alternative spellings or
  re-exports, and circular justifications through declarations that depend on it are
  excluded. The judges added after Opus use this version.

### Definition indicator

- **`definition-fidelity`**: a definition does not faithfully formalize the mathematical
  object its docstring describes. Either it is `incorrect` (it defines something else) or
  `too_narrow` (the right object in less generality than its natural one, e.g. on `ℝ^d`
  when it makes sense in any Banach space, or with stronger hypotheses than the
  construction uses). A definition without a docstring is flagged
  `no_docstring` by rule, without a judge. Definitions the judge classes as technical
  devices with no mathematical counterpart are set aside.

### File audits

One complete source file at a time, against one rubric
([`audits/file-quality-v1/`](audits/file-quality-v1/README.md)). Four audits enter the
main reports:

- **`statement-generality`**: a statement admits a useful more general form, such as a
  class of fields instead of a concrete scalar type, or a weaker structural assumption.
- **`vacuity-and-misstatement`**: a result fails to express its documented purpose: it is
  vacuous through inconsistent assumptions or an empty domain, or misses a condition or
  conclusion.
- **`repeated-proof-machinery`**: nontrivial reasoning repeated in at least two proofs,
  which a shared lemma would make more readable and maintainable.
- **`readable-proof-simplification`**: a proof that can be simplified without becoming
  harder to read.

Two more rubrics, **`concept-reinvention`** (a competing version of a Mathlib concept)
and **`simp-interface`** (problems with the simp lemmas of a file), are not ready for use:
a review of a sample of their flags found many that the rubric should not allow
([appendix](AUDIT_APPENDIX.md)).

## Judges

| Short name | Model | Run through |
|---|---|---|
| Opus | `claude-opus-5-5` | Claude Code (`claude -p`) |
| Sonnet | `claude-sonnet-5-5` | Claude Code (`claude -p`) |
| Sol | `gpt-6.1-sol` | Codex CLI (`codex exec`) |
| Luna | `gpt-6-luna` | Codex CLI (`codex exec`) |
| DeepSeek | DeepSeek V4.1 Flash | OpenRouter, pinned to the InferenceNet FP8 provider |

All run at high effort. Coverage differs: Opus judged 1000 theorems and 1000 definitions
per library of the first five libraries, the other judges smaller samples, and the newer
corpora have smaller samples still. [AUDIT_RESULTS.md](AUDIT_RESULTS.md) gives the
coverage of every cell.

## Methodology

### Sampling

- **Theorems and definitions** are found by [leanscan.py](scripts/leanscan.py), a
  syntactic scanner that assumes top-level commands start at column 0. The sample is
  uniform over the eligible declarations of each library, so larger projects and files
  weigh in proportion to their number of declarations. Each index is drawn with a fixed
  seed and redrawn if already taken, so a longer draw starts with the shorter one and a
  sample can be extended. `runs/main` uses seed 0 (theorems), `runs/defs1` seed 1
  (definitions).
- **Files** are eligible if they contain a mathematical declaration keyword at the start
  of a command (comments and strings masked; a syntactic filter, not elaboration). They
  are ordered by a SHA-256 hash of the seed, library and path, and the first ones are
  taken. Files are not weighted by size.

### What the judge sees

- **Theorems and definitions**: a snippet with the enclosing `namespace`/`section`
  commands and the `variable`, `open`, `universe`, `include`, `omit`, `set_option`, local
  attribute/instance and notation commands in effect, then the declaration and its proof.
  Theorem docstrings are removed; definition docstrings are kept, since the definition is
  judged against them.
- **Files**: the whole file, comments and private declarations included.
- **Readable sources**: the library itself, Mathlib, Batteries and Lean core.
  `unnecessary-hypotheses` reads Mathlib master at the commit pinned for the corpus;
  the other indicators and the file audits read the Mathlib and Batteries versions each
  library pins, so that a lemma added to Mathlib later does not count.

### Judge protocol

- One fresh session per target and audit, with no memory of other targets or of earlier
  verdicts.
- Read-only access to the allowed directories through three tools: Read, Grep and Glob.
  No Lean, shell, web access or writing. Project and user customisations are disabled.
  Codex judges get the same three tools from a path-restricted server; DeepSeek gets them
  from a custom harness.
- The answer follows a JSON schema and is validated before it is accepted. File-audit
  findings must quote the file, and the quotes and line ranges are checked against the
  sources.
- Each judge run (a *label*) records its model, effort, CLI version and the hashes of the
  prompt, schema, corpus lock and runner (`judge.json`), so that verdicts from different
  protocols are never mixed. Failed calls are retried and never count as negative
  verdicts.

### Scoring

A target is flagged if the judge reports at least one finding. Each library gets its
flagged / judged count with a Wilson 95% interval, using the first pass of each judge.
Combined summaries take the union of findings over several audits, counted over the
targets that every contributing audit has reviewed. Agreement between judges is the
correlation of their flag decisions on shared targets, with bootstrap intervals. Costs
are what the tokens would cost at API rates, whether or not a subscription paid for them.
[AUDIT_METHODS.md](AUDIT_METHODS.md) has the details.

### Checks of the judges

- **Test-retest**: blind second runs of the same judge on the same targets, for Opus
  ([agreement](runs/main/unnecessary-hypotheses/rejudge-claude-opus-5-5-high/agreement-full.md))
  and for Sol, Sonnet and Luna (`*-repeat-2` labels), on `unnecessary-hypotheses`.
- **Agreement between models**: the correlation matrices of
  [AUDIT_RESULTS.md](AUDIT_RESULTS.md).
- **Adversarial verifier** ([verify.py](scripts/verify.py),
  [prompt](indicators/unnecessary-hypotheses-verify/prompt.md)): a second judge shown the
  first judge's claims. It confirmed every claim it was shown, so it is not used as a
  filter.
- **Definition fidelity**: a sensitivity test
  ([`runs/defs-sensitivity`](runs/defs-sensitivity/definition-fidelity/claude-opus-5-5-high/report.md),
  definitions picked in [sensitivity.txt](indicators/definition-fidelity/sensitivity.txt))
  on definitions written in a narrower setting than a Mathlib counterpart, and a mutation
  test ([`runs/defs-mutants`](runs/defs-mutants/), spec in
  [mutations.json](indicators/definition-fidelity/mutations.json)): definitions judged
  faithful are made wrong by a one-line, type-preserving change, keeping their
  docstrings, among unchanged controls. Score it with
  `python3 scripts/mutate.py --spec indicators/definition-fidelity/mutations.json --run defs-mutants --score`.
- **Hand reviews** of flags:
  [`runs/file-quality-pilot-2026-10-21/reviews/`](runs/file-quality-pilot-2026-10-21/reviews/),
  and the [source review](runs/library-quality-scale-2026-10-26/sample-review-2026-10-27.json)
  behind moving two file audits to the appendix.
- **Repeated proof machinery validation**
  ([report](runs/repeated-machinery-validation-2026-10-27/validation-report.md)): a second
  judge tries to refute 20 flagged files per library and to find missed findings in 10
  unflagged ones.

### Limitations

- A flag is the judge's claim. Flags were checked by hand only on small samples, and no
  proposed change was compiled in Lean.
- Two runs of the same model can share blind spots, and models agree less on some audits
  than on others.
- The scanner and the file filter are syntactic.
- Uniform sampling describes the typical declaration or file of a library, which weighs
  its largest projects most.
- Coverage differs between judges, audits and corpora: compare cells with their sample
  sizes in mind.

## Repository layout

| Path | Content |
|---|---|
| `libraries.toml`, `libraries.lock.json` | The first five libraries: sources, included directories, exclusions, pinned commits |
| `indicators/<name>/` | Theorem and definition indicators: system prompt, per-target message, answer schema, settings |
| `audits/file-quality-v1/` | File audits: shared instructions, one rubric per audit, answer schema |
| `audits/repeated-machinery-validation-v1/` | Prompt of the repeated proof machinery validation |
| `scripts/` | Fetching, scanning, sampling, judging, reporting (see [RUNNING.md](RUNNING.md)) |
| `reports/` | The whitepaper |
| `pricing/` | Frozen API rates used for the cost estimates |
| `AUDIT_*.md`, `AUDIT_RESULTS.json` | Combined reports, generated by `scripts/audit_dashboard.py` |
| `runs/` | Samples, verdicts and reports of each experiment |

Experiments in `runs/`:

| Run | Content |
|---|---|
| [`main`](runs/main/) | 1000 theorems per library from the first five libraries (seed 0): theorem indicators, all judges |
| [`defs1`](runs/defs1/) | 1000 definitions per library from the first five libraries (seed 1): `definition-fidelity`, Opus |
| [`defs-sensitivity`](runs/defs-sensitivity/), [`defs-mutants`](runs/defs-mutants/) | Checks of the definition-fidelity judge |
| [`file-quality-pilot-2026-10-21`](runs/file-quality-pilot-2026-10-21/) | 10 files each from Mathlib, Tau Ceti and Lean Pool: all six file audits, Sonnet, Luna and DeepSeek |
| [`library-quality-scale-2026-10-26`](runs/library-quality-scale-2026-10-26/) | File audits extended to 372 files per library across six corpora, Sonnet |
| [`openai-math-2026-10-21`](runs/openai-math-2026-10-21/) | OpenAI Math: 2000 theorems and 2000 files selected, theorem and file audits |
| [`cfsg-pilot-2026-10-27`](runs/cfsg-pilot-2026-10-27/) | CFSG: 2000 theorems and 2000 files selected, theorem audits and repeated proof machinery |
| [`repeated-machinery-validation-2026-10-27`](runs/repeated-machinery-validation-2026-10-27/) | Validation of the repeated proof machinery flags |
| [`deepseek-pilot-2026-10-21`](runs/deepseek-pilot-2026-10-21/) | Selection and budget of the DeepSeek pilot; its verdicts are stored in the runs above |

Each run holds its sample (`samples.jsonl`, with library, commit, path, lines and a GitHub
link per target), the snippet or file each judge received, and one `results/<id>.json` per
verdict. The full session transcripts of the judges (every file each judge read or
searched) are not in the repository; ask for them if you need them.

## Reproducing and extending

```sh
python3 scripts/fetch.py --deps                     # clone the corpus at the pinned commits
python3 scripts/sample.py --run NAME --n 100 --seed 0   # draw 100 theorems per library
python3 scripts/judge.py --run NAME --jobs 8        # judge them (unnecessary-hypotheses)
python3 scripts/report.py --run NAME --label claude-opus-5-5-high
```

[RUNNING.md](RUNNING.md) has the requirements and full instructions: checking the sample
of `runs/main`, judging it with another model or agent, adding an indicator or a library,
the Codex and DeepSeek judges, the file audits and the runners of the newer corpora.
LLM verdicts vary between runs even with the same model and prompt, so a reproduction
should be judged by matching rates and high agreement, not identical verdicts.
