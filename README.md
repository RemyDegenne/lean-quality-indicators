# Quality indicators for AI-built Lean libraries

Sampled, LLM-judged quality indicators, compared across five Lean 4 libraries built on
Mathlib: Mathlib itself, [Tau Ceti](https://github.com/TauCetiProject/TauCeti),
[Lean Pool](https://github.com/Vilin97/lean-pool), the Anthropic
[FLT formalization](https://github.com/anthropics/fermats-last-theorem) and the 43 libraries
of [Formal Frontier](https://github.com/FormalFrontier).

Indicators (one directory each in `indicators/`):

- **`unnecessary-hypotheses`**: a hypothesis of a theorem (one of its binders, or one it
  takes from a `variable` command) that can be deleted, leaving a statement that is still
  true and provable, possibly with a different proof. Results below.
- **`duplicates-mathlib`**: the theorem is already in Mathlib (with Batteries and Lean core),
  either as the same statement up to presentation (`duplicate`) or as an instantiation of a
  single Mathlib declaration provable from it in one or two short lines (`special_case`).
  General principles of logic, equality and structure (`Eq.subst`, `map_add`, ext lemmas, …)
  applied to the library's own definitions do not count. Judged against the Mathlib version
  each library pins; not run on Mathlib itself. Results below.

All results come from experiment `runs/main`: corpus pinned in October 2026, judge
`claude-opus-5-5` at effort `high`, theorems sampled uniformly per library.

## Results so far: unnecessary hypotheses

1000 theorems per library:

| Library | Flagged / 1000 | Rate | 95% CI |
|---|---:|---:|---:|
| Mathlib | 31 | 3.1% | 2.2%–4.4% |
| Formal Frontier | 34 | 3.4% | 2.4%–4.7% |
| Tau Ceti | 68 | 6.8% | 5.4%–8.5% |
| Lean Pool | 150 | 15.0% | 12.9%–17.3% |
| FLT (Anthropic) | 203 | 20.3% | 17.9%–22.9% |

A second, independent run of the same judge on the first 300 theorems per library, blind to
the first verdicts, reproduces these rates within 1.3 points per library (Cohen's κ = 0.92):

| Library | Run 1 | Run 2 | Flagged in both runs | Flagged in either run | κ |
|---|---:|---:|---:|---:|---:|
| Mathlib | 11 (3.7%) | 9 (3.0%) | 9 (3.0%, 1.6–5.6%) | 11 (3.7%) | 0.90 |
| Tau Ceti | 15 (5.0%) | 14 (4.7%) | 14 (4.7%, 2.8–7.7%) | 15 (5.0%) | 0.96 |
| Formal Frontier | 15 (5.0%) | 15 (5.0%) | 14 (4.7%, 2.8–7.7%) | 16 (5.3%) | 0.93 |
| Lean Pool | 52 (17.3%) | 48 (16.0%) | 47 (15.7%, 12.0–20.2%) | 53 (17.7%) | 0.93 |
| FLT (Anthropic) | 64 (21.3%) | 64 (21.3%) | 59 (19.7%, 15.6–24.5%) | 69 (23.0%) | 0.90 |

These are the judges' verdicts. Their correctness has been checked by hand only on a handful
of flags (all correct), not by compiling the proposed changes in Lean; two runs of the same
model can share blind spots.

## Results so far: duplicates of Mathlib

1000 theorems per library. A *wrapper* is a finding whose proof already applies the Mathlib
declaration (the library restates a Mathlib result in its own terms); a *re-derived* finding
proves the Mathlib result another way.

| Library | Findings / 1000 | Rate (95% CI) | `duplicate` | `special_case` | Wrappers | Re-derived (95% CI) |
|---|---:|---:|---:|---:|---:|---:|
| Formal Frontier | 46 | 4.6% (3.5–6.1%) | 5 | 41 | 29 | 17: 1.7% (1.1–2.7%) |
| Tau Ceti | 50 | 5.0% (3.8–6.5%) | 0 | 50 | 34 | 16: 1.6% (1.0–2.6%) |
| Lean Pool | 68 | 6.8% (5.4–8.5%) | 8 | 60 | 28 | 40: 4.0% (3.0–5.4%) |
| FLT (Anthropic) | 137 | 13.7% (11.7–16.0%) | 12 | 125 | 51 | 86: 8.6% (7.0–10.5%) |

Judge verdicts, not yet audited beyond a 40-theorem test, and not yet test-retested.

## Repository layout

| Path | Content |
|---|---|
| `libraries.toml` | The corpus: each library as a set of git sources, with included directories and exclusions |
| `libraries.lock.json` | The commit of each of the 47 source repositories |
| `scripts/fetch.py` | Clones the sources into `repos/` at the pinned commits, and with `--deps` the Mathlib and Batteries versions they pin |
| `scripts/leanscan.py` | Syntactic Lean scanner: finds the theorems and rebuilds the context of each |
| `scripts/sample.py` | Builds the population of each library and draws a seeded uniform sample |
| `scripts/judge.py` | Runs a judge (headless Claude Code) on each sampled theorem, or exports its inputs |
| `scripts/stats.py` | Progress of a judge run |
| `scripts/report.py` | Flag rates, confidence intervals and the list of flags of a judge run |
| `scripts/agreement.py` | Compares two judge runs on the same theorems (test-retest) |
| `scripts/verify.py` | Adversarial second judge that sees the first judge's claims |
| `scripts/indicator.py` | Reads an indicator's `config.toml` |
| `indicators/<name>/` | Judge prompt (`prompt.md`), per-theorem message (`message.md`), answer schema (`schema.json`), settings (`config.toml`) |
| `runs/main/` | The current experiment: sample, snippets, verdicts and reports |

## Requirements

- Python ≥ 3.11 (standard library only) and git.
- About 1.5 GB of disk for the clones, plus 0.8 GB for the pinned Mathlib and Batteries
  versions (`fetch.py --deps`, needed by indicators with `mathlib = "pinned"`).
- To run the judges as we did: [Claude Code](https://claude.com/claude-code) ≥ 2.1.280,
  logged in (the runner calls `claude -p`; no API key needed with a subscription).
- Optional: the Lean toolchains the libraries use, installed with
  [elan](https://github.com/leanprover/elan), so the judges can read the Lean core sources:
  `elan toolchain install leanprover/lean4:v4.36.0-rc1` (Mathlib, Tau Ceti), `v4.35.0-rc3`
  (Lean Pool), `v4.34.0-rc2` (Formal Frontier), `v4.33.1` (FLT). Nothing is built.

## Running an experiment

1. **Corpus.** `python3 scripts/fetch.py` clones every source at its pinned commit.
   `python3 scripts/fetch.py --update` moves every source to its latest commit and rewrites
   the lock instead (a new corpus, so start a new run). `--deps` also clones, under
   `repos/deps/`, the Mathlib and Batteries commits that each source pins in its
   `lake-manifest.json`. To add a library, add it to `libraries.toml` and run `fetch.py`.
2. **Sample.** `python3 scripts/sample.py --run NAME --n N --seed S` draws N theorems per
   library into `runs/NAME/`. `--extend --n M` adds M more per library to an existing run,
   from the same seeded draw, so the union is exactly what one draw of N + M would give.
   `--population-only` prints the population sizes; `--diagnose` also lists column-0 words
   the scanner does not recognise as commands.
3. **Judge.** `python3 scripts/judge.py --run NAME --jobs 8` judges every sample with the
   `unnecessary-hypotheses` indicator (`--indicator NAME` for another). Options: `--model`, `--effort`, `--label` (results go
   to `runs/NAME/<indicator>/<label>/results/`, default label `<model>-<effort>`), `--libs`,
   `--ids`, `--limit`, `--claude PATH` (Claude Code executable). Rerunning the same command
   resumes: judged samples are skipped and failed calls retried.
   `python3 scripts/stats.py --run NAME [--indicator NAME] --label LABEL` shows progress.
4. **Report.** `python3 scripts/report.py --run NAME [--indicator NAME] --label LABEL` writes
   `runs/NAME/<indicator>/LABEL/report.md`.
5. **Checks.** For a test-retest, judge the same run again under another label and compare:
   `python3 scripts/agreement.py --run NAME --first LABEL1 --second LABEL2` (all theorems
   judged by both), or with `--ids-file` for a selection. `python3 scripts/verify.py --run NAME
   --of LABEL` sends every flag, with its claims, to an adversarial verifier.

A new indicator is a directory `indicators/<name>/` with `prompt.md` (system prompt),
`message.md` (user message, with the placeholders `{snippet}`, `{name}`, `{line}`, `{path}`
and `{dirs}`), `schema.json` (answer schema, with a string field `verdict`) and
`config.toml`:

```toml
positive = ["duplicate", "special_case"]  # verdicts that count as findings
mathlib = "pinned"  # Mathlib the judge reads: "master" (repos/mathlib) or "pinned"
skip_libraries = ["mathlib"]  # libraries the indicator does not apply to
```

`report.py`, `stats.py` and `agreement.py` count the `positive` verdicts; the report lists
the other fields of each finding.

## Reproducing the current experiment

`runs/main` holds 1000 theorems per library (5000 in all), drawn with seed 0 in batches
(`--n 100`, then `--extend` with 100, 100, 100, 300 and 300 per library), which gives exactly
the sample of a single `--n 1000` draw. Coverage of the judge runs:

| Indicator | Label | Theorems |
|---|---|---|
| `unnecessary-hypotheses` | `claude-opus-5-5-high` | all 1000 per library |
| `unnecessary-hypotheses` | `rejudge-claude-opus-5-5-high` (blind second run) | the first 300 per library |
| `duplicates-mathlib` | `claude-opus-5-5-high` | all 1000 per library, Mathlib excepted |

1. Clone this repository and fetch the corpus at the pinned commits, with the pinned Mathlib
   and Batteries versions that `duplicates-mathlib` needs:

   ```sh
   python3 scripts/fetch.py --deps
   ```

2. Optionally, check that the sample is what the scripts draw (scanning the corpus takes
   about a minute on a multicore machine):

   ```sh
   python3 scripts/sample.py --run check --n 1000 --seed 0
   python3 -c "import json; k=lambda f: sorted((r['id'], r['path'], r['line']) for r in map(json.loads, open(f))); print(k('runs/main/samples.jsonl') == k('runs/check/samples.jsonl'))"
   ```

3. Judge the same theorems with your judge, under a new label (add `--indicator
   duplicates-mathlib` for the second indicator, and `--limit 400` to judge only the first
   400 per library).

   - **With Claude Code**, using our runner:

     ```sh
     python3 scripts/judge.py --run main --label my-run --jobs 8 [--model ...] [--effort ...]
     ```

   - **With another agent**, export what each judge session receives:

     ```sh
     python3 scripts/judge.py --run main --export export/ [--indicator ...]
     ```

     This writes `export/system-prompt.md`, `export/schema.json`, one user message per
     theorem in `export/messages/<id>.md`, and `export/jobs.jsonl` with, for each theorem, its
     `id`, `lib`, `message` file, working directory `cwd` and other readable directories
     `read_dirs` (absolute paths on your machine, so export after fetching). Our protocol is:
     one fresh session per theorem, with no memory of the others; the system prompt and the
     message as given; read-only file access (read, search, list) to `cwd` and `read_dirs`
     and nothing else (no Lean, no web, no writing); an answer in the JSON format of
     `schema.json`. The prompt names the tools Read, Grep and Glob; if your agent's tools are
     different, change that sentence and record the change. Save each answer, with the
     theorem's `id` and `lib` added, as
     `runs/main/<indicator>/my-run/results/<id>.json`:

     ```json
     {"id": "mathlib-0000", "lib": "mathlib", "verdict": "none_found", "hypotheses": []}
     ```

4. Compare with our runs:

   ```sh
   python3 scripts/report.py --run main [--indicator ...] --label my-run
   python3 scripts/agreement.py --run main [--indicator ...] --first claude-opus-5-5-high --second my-run
   ```

LLM verdicts vary between runs even with the same model and prompt: our two runs of the same
judge agree on 98% of theorems (κ = 0.92), and differ by up to 1.3 points per library. A
reproduction should be read as matching rates and high agreement, not identical verdicts.

### Files of the current experiment

All under `runs/main/`:

- `samples.jsonl`: the 5000 sampled theorems (library, repository, commit, path, lines,
  name, GitHub link); `samples/<lib>/<id>.lean`: the snippet each judge received; `run.json`:
  seed, population sizes, commits, batches.
- `unnecessary-hypotheses/claude-opus-5-5-high/`: first run. `results/<id>.json` per theorem;
  `report.md` (1000 per library), `report-400.md`, `report-batch3.md`, `report-batch2.md`,
  `report-batch1.md` (400, 300, 200, 100 per library).
- `unnecessary-hypotheses/claude-opus-5-5-high/verify/claude-opus-5-5-high/`: adversarial
  verification of the 157 flags among the first 300 per library (it confirmed all 235
  claims, so it does not discriminate; kept for the record).
- `unnecessary-hypotheses/rejudge-claude-opus-5-5-high/`: blind second run on the first 300
  per library. `report.md`; `agreement-full.md` (comparison with the first run, every
  disagreement); `agreement.md` (the 157 flags plus 157 random non-flags, selected in
  `rejudge-ids.json`).
- `duplicates-mathlib/claude-opus-5-5-high/`: `results/<id>.json` per theorem; `report.md`
  (1000 per library), `report-400.md`, `report-700.md`. The first 10 theorems per library
  were judged in the test of the final prompt, the rest in the full run (the runner judges
  the libraries in turn, so progress is even across them).

The full session transcripts of the judges (about 140 MB: every file each judge read or
searched) are not in the repository; ask for them if you need them.

## Corpus and sampling decisions

- **Population.** Every `theorem` and `lemma` in the included files, found by
  `scripts/leanscan.py`, a syntactic scanner that assumes top-level commands start at column
  0. Deprecated and `private` declarations are skipped (private helpers often carry
  normalising hypotheses set up by their caller). Population sizes:

  | Library | Eligible theorems |
  |---|---:|
  | Mathlib | 187,171 |
  | Tau Ceti | 135,838 |
  | Lean Pool | 233,671 |
  | FLT (Anthropic) | 433,929 |
  | Formal Frontier | 10,318 |

- **Mathlib**: `Mathlib/` without `Tactic`, `Util`, `Lean`, `Testing`, `Deprecated`.
- **Formal Frontier**: the main `lean_lib` of each of the 43 library repositories of the
  GitHub organisation (not `pod`, not the Sutherland drafts, not the Test/Examples
  libraries).
- **FLT**: `P2M/Sol`, `P2M/Derive`, `Definitions`. The `Theorems/Thm_*.lean` wrappers are
  skipped because each restates a `solution` theorem of `P2M/Sol` and delegates its proof to
  it. About 93% of the population are helper lemmas of the `P2M/Sol` proofs.
- **Everywhere**: `*/Certificates/*` is excluded (about 81K generated numerical checks in
  Lean Pool, which would otherwise be 22% of its sample).
- **Sampling** is uniform over theorems within each library, so larger projects and files
  weigh in proportion to their number of theorems.
- **Snippet.** Each sampled theorem is shown with the enclosing `namespace`/`section`
  commands and the `variable`, `open`, `universe`, `include`, `omit`, `set_option`, local
  attribute/instance and notation commands in effect, then the theorem and its proof, with
  its docstring removed. The judge can read the library's source (docstring included),
  Mathlib and Lean core: for `unnecessary-hypotheses` the pinned Mathlib master commit, for
  `duplicates-mathlib` the Mathlib and Batteries versions each library depends on.

## Costs

The `cost_usd` fields are what the same tokens would cost at API rates, as reported by
`claude -p`; with a Claude subscription, the runs draw on its usage quota instead. The first
`unnecessary-hypotheses` run cost about $374 for 5000 theorems (a median of 3 agent turns
per theorem), its second run $108 for 1500; the `duplicates-mathlib` run about $216 for 4000.
