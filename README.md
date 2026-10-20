# Quality indicators for AI-built Lean libraries

Sampled, LLM-judged quality indicators, compared across five Lean 4 libraries built on
Mathlib: Mathlib itself, [Tau Ceti](https://github.com/TauCetiProject/TauCeti),
[Lean Pool](https://github.com/Vilin97/lean-pool), the Anthropic
[FLT formalization](https://github.com/anthropics/fermats-last-theorem) and the 43 libraries
of [Formal Frontier](https://github.com/FormalFrontier).

The first indicator is **unnecessary hypotheses**: a hypothesis of a theorem (one of its
binders, or one it takes from a `variable` command) that can be deleted, leaving a statement
that is still true and provable, possibly with a different proof.

## Results so far

Experiment `runs/main` (corpus pinned in October 2026, judge `claude-opus-5-5` at effort
`high`, 400 theorems sampled uniformly per library):

| Library | Flagged / 400 | Rate | 95% CI |
|---|---:|---:|---:|
| Mathlib | 15 | 3.8% | 2.3%–6.1% |
| Formal Frontier | 17 | 4.2% | 2.7%–6.7% |
| Tau Ceti | 23 | 5.8% | 3.9%–8.5% |
| Lean Pool | 61 | 15.2% | 12.1%–19.1% |
| FLT (Anthropic) | 82 | 20.5% | 16.8%–24.7% |

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

## Repository layout

| Path | Content |
|---|---|
| `libraries.toml` | The corpus: each library as a set of git sources, with included directories and exclusions |
| `libraries.lock.json` | The commit of each of the 47 source repositories |
| `scripts/fetch.py` | Clones the sources into `repos/` at the pinned commits |
| `scripts/leanscan.py` | Syntactic Lean scanner: finds the theorems and rebuilds the context of each |
| `scripts/sample.py` | Builds the population of each library and draws a seeded uniform sample |
| `scripts/judge.py` | Runs a judge (headless Claude Code) on each sampled theorem, or exports its inputs |
| `scripts/stats.py` | Progress of a judge run |
| `scripts/report.py` | Flag rates, confidence intervals and the list of flags of a judge run |
| `scripts/agreement.py` | Compares two judge runs on the same theorems (test-retest) |
| `scripts/verify.py` | Adversarial second judge that sees the first judge's claims |
| `indicators/<name>/` | Judge prompt (`prompt.md`), per-theorem message (`message.md`), answer schema (`schema.json`) |
| `runs/main/` | The current experiment: sample, snippets, verdicts and reports |

## Requirements

- Python ≥ 3.11 (standard library only) and git.
- About 1.5 GB of disk for the clones.
- To run the judges as we did: [Claude Code](https://claude.com/claude-code) ≥ 2.1.280,
  logged in (the runner calls `claude -p`; no API key needed with a subscription).
- Optional: the Lean toolchains the libraries use, installed with
  [elan](https://github.com/leanprover/elan), so the judges can read the Lean core sources:
  `elan toolchain install leanprover/lean4:v4.36.0-rc1` (Mathlib, Tau Ceti), `v4.35.0-rc3`
  (Lean Pool), `v4.34.0-rc2` (Formal Frontier), `v4.33.1` (FLT). Nothing is built.

## Running an experiment

1. **Corpus.** `python3 scripts/fetch.py` clones every source at its pinned commit.
   `python3 scripts/fetch.py --update` moves every source to its latest commit and rewrites
   the lock instead (a new corpus, so start a new run). To add a library, add it to
   `libraries.toml` and run `fetch.py`.
2. **Sample.** `python3 scripts/sample.py --run NAME --n N --seed S` draws N theorems per
   library into `runs/NAME/`. `--extend --n M` adds M more per library to an existing run,
   from the same seeded draw, so the union is exactly what one draw of N + M would give.
   `--population-only` prints the population sizes; `--diagnose` also lists column-0 words
   the scanner does not recognise as commands.
3. **Judge.** `python3 scripts/judge.py --run NAME --jobs 8` judges every sample with the
   `unnecessary-hypotheses` indicator. Options: `--model`, `--effort`, `--label` (results go
   to `runs/NAME/<indicator>/<label>/results/`, default label `<model>-<effort>`), `--libs`,
   `--ids`, `--limit`, `--claude PATH` (Claude Code executable). Rerunning the same command
   resumes: judged samples are skipped and failed calls retried.
   `python3 scripts/stats.py --run NAME --label LABEL` shows progress.
4. **Report.** `python3 scripts/report.py --run NAME --label LABEL` writes
   `runs/NAME/<indicator>/LABEL/report.md`.
5. **Checks.** For a test-retest, judge the same run again under another label and compare:
   `python3 scripts/agreement.py --run NAME --first LABEL1 --second LABEL2` (all theorems
   judged by both), or with `--ids-file` for a selection. `python3 scripts/verify.py --run NAME
   --of LABEL` sends every flag, with its claims, to an adversarial verifier.

A new indicator is a directory `indicators/<name>/` with `prompt.md` (system prompt),
`message.md` (user message, with the placeholders `{snippet}`, `{name}`, `{line}`, `{path}`
and `{dirs}`) and `schema.json` (answer schema), used with `judge.py --indicator <name>`.
`report.py`, `stats.py` and `agreement.py` currently count the verdict
`unnecessary_hypothesis_found`; adapt them for an indicator with other verdicts.

## Reproducing the current experiment

`runs/main` was drawn with seed 0 in four batches of 100 theorems per library
(`--n 100`, then `--extend --n 100` three times), which gives exactly the sample of a single
`--n 400` draw. The first judge run (`claude-opus-5-5-high`) covers all 2000 theorems; the
blind second run (`rejudge-claude-opus-5-5-high`) covers the first 300 per library.

1. Clone this repository and fetch the corpus at the pinned commits:

   ```sh
   python3 scripts/fetch.py
   ```

2. Optionally, check that the sample is what the scripts draw (scanning the corpus takes
   about a minute on a multicore machine):

   ```sh
   python3 scripts/sample.py --run check --n 400 --seed 0
   python3 -c "import json; k=lambda f: sorted((r['id'], r['path'], r['line']) for r in map(json.loads, open(f))); print(k('runs/main/samples.jsonl') == k('runs/check/samples.jsonl'))"
   ```

3. Judge the same 2000 theorems with your judge, under a new label.

   - **With Claude Code**, using our runner:

     ```sh
     python3 scripts/judge.py --run main --label my-run --jobs 8 [--model ...] [--effort ...]
     ```

   - **With another agent**, export what each judge session receives:

     ```sh
     python3 scripts/judge.py --run main --export export/
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
     `runs/main/unnecessary-hypotheses/my-run/results/<id>.json`:

     ```json
     {"id": "mathlib-0000", "lib": "mathlib", "verdict": "none_found", "hypotheses": []}
     ```

4. Compare with our runs:

   ```sh
   python3 scripts/report.py --run main --label my-run
   python3 scripts/agreement.py --run main --first claude-opus-5-5-high --second my-run
   ```

LLM verdicts vary between runs even with the same model and prompt: our two runs of the same
judge agree on 98% of theorems (κ = 0.92), and differ by up to 1.3 points per library. A
reproduction should be read as matching rates and high agreement, not identical verdicts.

### Files of the current experiment

All under `runs/main/`:

- `samples.jsonl`: the 2000 sampled theorems (library, repository, commit, path, lines,
  name, GitHub link); `samples/<lib>/<id>.lean`: the snippet each judge received; `run.json`:
  seed, population sizes, commits, batches.
- `unnecessary-hypotheses/claude-opus-5-5-high/`: first run. `results/<id>.json` per theorem;
  `report.md` (400 per library), `report-batch1.md`, `report-batch2.md`, `report-batch3.md`
  (100, 200, 300 per library).
- `unnecessary-hypotheses/claude-opus-5-5-high/verify/claude-opus-5-5-high/`: adversarial
  verification of the 157 flags among the first 300 per library (it confirmed all 235
  claims, so it does not discriminate; kept for the record).
- `unnecessary-hypotheses/rejudge-claude-opus-5-5-high/`: blind second run on the first 300
  per library. `report.md`; `agreement-full.md` (comparison with the first run, every
  disagreement); `agreement.md` (the 157 flags plus 157 random non-flags, selected in
  `rejudge-ids.json`).

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
  Mathlib (the pinned master commit) and Lean core.

## Costs

The `cost_usd` fields are what the same tokens would cost at API rates, as reported by
`claude -p`; with a Claude subscription, the runs draw on its usage quota instead. The first
run cost about $146 for 2000 theorems (a median of 3 agent turns per theorem), the second
$108 for 1500.
