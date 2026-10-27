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
- **`definition-fidelity`**: a definition (`def`, `abbrev`, `structure`, `class`) that does
  not faithfully formalize the mathematical object its docstring describes: `incorrect` (it
  defines something else) or `too_narrow` (the right object in a narrower generality than its
  natural one, e.g. on `ℝ^d` when it makes sense in any Banach space, or with stronger
  hypotheses than the construction uses). A definition without a docstring is flagged
  `no_docstring` by rule, without a judge. Results below.

The theorem indicators come from experiment `runs/main` and the definition indicator from
`runs/defs1`: corpus pinned in October 2026, judge `claude-opus-5-5` at effort `high`,
declarations sampled uniformly per library.

### Sol, Luna and Sonnet reproduction

This fork adds a Codex backend while retaining the Claude Code backend. The comparison
uses **the original first 300 samples per library**, not all 1000 now stored in `runs/main`.
No sampling or corpus update is needed. Fetch exactly the locked source commits:

```sh
python3 scripts/fetch.py
python3 -m unittest discover -s scripts -v
CODEX_BIN="$PWD/scripts/codex_rate_guard.py" \
  python3 -u scripts/benchmark.py --sol-jobs 1 --luna-jobs 1 --sonnet-jobs 2 --passes 2
```

The benchmark runs `gpt-6.1-sol`, `gpt-6-luna` and `claude-sonnet-5-5`, all at `high`
effort, twice independently: 9000 judgments. `--jobs` is default concurrency **per model**
(default 1); `--sol-jobs`, `--luna-jobs` and `--sonnet-jobs` override each model separately.
The example uses a shared rate guard: Sol and Luna share **one active Codex session**,
with starts spaced at least ten seconds apart. A runtime HTTP 429 aborts active attempts,
halves the concurrency limit, and sets
a five-minute cooldown shared by both models. Internal Codex reconnect errors are
checked even when a later retry might have succeeded. Sonnet runs two sessions separately.
Without the wrapper, `--jobs` counts independent sessions for each model. Use saved Codex
and Claude Code login credentials. The guard state and events are stored in ignored
`codex-rate-guard-*.log` files beside the results.

To tune concurrency, start larger worker pools behind the guard; these are queued
workers, not simultaneous model sessions. In another terminal run the controller:

```sh
CODEX_BIN="$PWD/scripts/codex_rate_guard.py" \
  python3 -u scripts/benchmark.py --sol-jobs 8 --luna-jobs 8 --sonnet-jobs 2 --passes 2
python3 -u scripts/tune_codex.py --minutes 45 --max-sessions 8 --spacing 5
```

The controller raises shared Sol/Luna concurrency by one after five clean minutes with
at least four completed judgments. Starts are staggered. A 429 immediately halves the
shared limit, cancels active Codex attempts and imposes a five-minute cooldown; waiting
workers make no requests. The controller records throughput at each stage and retains
the fastest validated setting, backing down if additional concurrency stops improving it.
It does not raise past a setting that produced a 429 during that tuning period. This
finds a demonstrated stable setting for the observed workload, not a permanent rate-limit
guarantee. The guard continues to back off on 429s after tuning ends. Detailed session
and tuning events remain in the ignored log files alongside the results.

After choosing a validated ceiling, the same controller can maintain it for the rest
of the run, for example `python3 -u scripts/tune_codex.py --minutes 720 --max-sessions 9
--spacing 3`. It never raises above that ceiling, backs off on rate errors, and exits
when the benchmark's completion marker appears.

The [2026-10-20 tuning measurements](runs/main/unnecessary-hypotheses/rate-tuning.json)
selected nine shared Sol/Luna sessions with three-second start spacing: 16 theorems/minute
combined, versus 16.2 at ten sessions. No 429s were observed during 61.6 minutes of
supervised tuning. These are throughput measurements, not completed quality-audit results.

Install Codex CLI (tested with 0.163.0), Claude Code (tested with 2.1.304), Python 3.11+
and ripgrep. For complete Lean core access, install the four toolchains listed below.
No Lean code is executed or built. Keep the same toolchains installed throughout the run.

To pilot a single model on five samples per library, or resume its full pass:

```sh
python3 scripts/judge.py --run main --backend codex --model gpt-6.1-sol \
  --label pilot-sol --limit 5 --jobs 4
python3 scripts/judge.py --run main --backend codex --model gpt-6-luna \
  --label gpt-6-luna-high --limit 300 --jobs 12
python3 scripts/judge.py --run main --model claude-sonnet-5-5 \
  --label claude-sonnet-5-5-high --limit 300 --jobs 12
```

Each Codex theorem starts a fresh ephemeral session with the indicator prompt replacing
the built-in coding instructions. The only prompt text change replaces
`with the Read, Grep and Glob tools` with `with the sources MCP tools Read, Grep and Glob`.
The source MCP server exposes those three tools and resolves every requested path against
the explicit permitted roots, including protection against symlink escapes. Read defaults
to 400 lines (up to 2000 per call), Glob to 1000 files, and tool output to 60000 characters;
the judge can paginate or narrow its search. There is no shell or web access. Automatic
project instructions, skills, memory, plugins and unrelated integrations are disabled.
The judge cannot read previous verdicts or reports through the source tools. Claude uses
the original three built-in tools and prompt, plus `--restricted` to enforce its source
directory boundary. A denied Codex source tool approval invalidates the judgment.

Each label saves `judge.json` with the model, effort, CLI version and hashes of the
prompt, schema, corpus lock and runner code. Changing this protocol requires a new label.
Results are written atomically; interrupted runs resume by skipping completed verdicts.
Failed calls produce logs, never negative verdicts. Attempt transcripts and stderr are
kept locally and ignored by git. Codex token usage is recorded; its dollar cost is
unknown rather than reported as zero. Claude reports API-equivalent cost even when its
subscription supplies the quota.

The benchmark produces per-pass reports, disagreement reports against both Opus passes,
and `runs/main/unnecessary-hypotheses/model-comparison.md`: flag rates with Wilson
intervals and all pairwise comparisons (both/either flags, disagreements, matching
hypotheses and Cohen's kappa). It refuses to publish that comparison until every selected
theorem has a verdict. Rerun the same benchmark command to resume after failures.
Pilot labels are separate and are excluded from the final comparison.

### Duplicate reproduction including Mathlib

`duplicates-mathlib-inclusive` retains the original pinned-Mathlib duplicate and
special-case criteria and includes Mathlib's own samples. A match must be a distinct
declaration: the target itself, alternative spellings or re-exports of it, and circular
justifications through declarations that depend on the target are excluded. Judges must
inspect candidate proofs to establish independence. This is an LLM judgment, without Lean
execution, and requires later auditing. The original `duplicates-mathlib` protocol is intact.

The queued reproduction uses the same 1000 samples per library, once each for Sol 6.1,
Luna 6 and Sonnet 5.5, all at high effort: 15,000 judgments including the new Mathlib arm.

```sh
python3 scripts/fetch.py --deps
python3 -u scripts/duplicates_benchmark.py --slow-spacing 180 --limit 1000
```

Before the hypothesis benchmark writes its success marker, each model starts at most one
duplicate session per three minutes, with one active duplicate session per model. The full
sample selection is recorded from the outset; early judgments are retained. After the
marker, waiting workers automatically use the full profile: eight queued workers per Codex
model behind the existing **nine-session shared guard**, and two Sonnet sessions. Hypothesis
and duplicate Codex sessions share that same guard throughout, including live 429 detection,
halving of the shared limit and a five-minute cooldown. Maintenance checks run every minute
and recover gradually within the ceiling after backoff.

`runs/main/duplicates-mathlib-inclusive/status.json` records progress and worker status
every minute. `pace-events.log` records slow/full admissions. Each label retains its own
protocol manifest, verdicts and transcripts. Completion generates per-model reports and a
comparison against the saved Opus duplicate judgments on the four external libraries;
Opus has no Mathlib baseline. Because the prompt adds self-match and circularity exclusions,
this is an explicitly modified replication. A success marker is written only when every
selected judgment and report is complete. Resuming skips saved verdicts.

### Small pilot of six file quality audits

The [file quality suite](audits/file-quality-v1/README.md) reviews the same ten complete
files each from Mathlib, Tau Ceti and Lean Pool against six separate rubrics. The
judge is Sonnet 5.5 at high effort, with two sessions total (180 independent judgments).
Samples, protocol snapshots and model results are separated so coverage and models can
be expanded without replacing the pilot data.

Repeated proof machinery has thirty completed Sonnet pilot reviews, using a concise
rubric requiring a shared lemma, a proof sketch and rewritten existing uses. Its
[results](runs/file-quality-pilot-2026-10-21/reports/claude-sonnet-5-5-high-structure-machinery/summary.md)
use the same file sample.
Every positive has an [individual source review](runs/file-quality-pilot-2026-10-21/reviews/repeated-machinery-2026-10-21.md).
Luna has completed all six audits on the same thirty files (180 blind reviews).

Concept reinvention and simp interface are **not ready for use** in library comparisons.
Their results are retained in the [appendix](AUDIT_APPENDIX.md), and excluded from the
main summaries. The four main file audits are statement generality, vacuity and
misstatement, repeated proof machinery, and readable proof simplification.

OpenAI Math has fixed selections of 2,000 theorem targets and 2,000 whole files from
`lean/OAI/`. Opus, Sol, Sonnet and Luna are judging the first 100 targets on each audit,
with two Sol sessions, one session each for the other models, and the shared Codex rate guard. Samples, protocols and
results live in `runs/openai-math-2026-10-21/`; all 42 pinned dependencies are available
as read-only sources. Resume with `python3 scripts/corpus_pilot.py judge --model Sol --jobs 2`.

Sonnet's unnecessary-hypothesis and Mathlib-duplication audits now continue to 300 targets,
adding targets 101–300 from the same frozen theorem selection. Its repeated-machinery
coverage already exceeds that level at 372 files. The
[theorem continuation](runs/openai-math-2026-10-21/scale-300/theorems/library-comparison.md)
preserves the first 100 judgments and joins the same first pass in the main reports.
Run `python3 scripts/openai_scale.py --prepare-only` to prepare, or omit the option to
resume with one Sonnet 5.5 high session on the lean-fro subscription. The continuation
has a $40 API-equivalent ceiling, refuses API-key billing and extra usage, and pauses
on rate-limit rejection. Worker and publication templates are `scripts/openai-scale*.service`.

## Results so far: unnecessary hypotheses

[Current reports for the seven main audits](AUDIT_RESULTS.md) give target/pass counts, flag
rates with Wilson 95% intervals, matched-target Pearson correlation matrices with paired
bootstrap intervals, and API-equivalent expenditure / estimated cost of one pass at the
largest completed model's scale. [Cost details](runs/main/api-equivalent-costs.md) include
rates and retained retry expenditure. Local reports refresh every five minutes while
the OpenAI Math runs finish; the committed reports are snapshots.

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

## Results so far: definition fidelity

1000 definitions per library (`runs/defs1`, seed 1). Definitions the judge classes as
technical devices with no mathematical counterpart (auxiliary constructions, internal data)
are set aside; the first rate is over the remaining *assessed* definitions, the second over
all 1000.

| Library | Set aside | Assessed | `incorrect` | `too_narrow` | `no_docstring` | Rate, assessed (95% CI) | Rate, all (95% CI) |
|---|---:|---:|---:|---:|---:|---:|---:|
| Mathlib | 170 | 830 | 2 | 6 | 2 | 1.2% (0.7–2.2%) | 1.0% (0.5–1.8%) |
| Tau Ceti | 88 | 912 | 1 | 10 | 0 | 1.2% (0.7–2.1%) | 1.1% (0.6–2.0%) |
| Formal Frontier | 231 | 769 | 0 | 29 | 12 | 5.3% (4.0–7.2%) | 4.1% (3.0–5.5%) |
| Lean Pool | 615 | 385 | 3 | 29 | 1 | 8.6% (6.2–11.8%) | 3.3% (2.4–4.6%) |
| FLT (Anthropic) | 0 | 1000 | 0 | 0 | 1000 | 100% (99.6–100%) | 100% (99.6–100%) |

FLT has no docstring on any of its definitions (0 out of 79,590 eligible), against 98.7–100%
coverage in the other libraries. The share set aside as technical differs widely: 62% of Lean
Pool's sampled definitions, 9–23% elsewhere.

Two checks of the judge (prompt and settings as in the run):

- **Sensitivity** (`runs/defs-sensitivity`, picked in
  `indicators/definition-fidelity/sensitivity.txt`): of 7 definitions written in a narrower
  setting than a Mathlib counterpart (e.g. a Frobenius norm on square `Fin n` real matrices),
  5 are flagged `too_narrow`; the 3 controls stay `faithful`.
- **Mutation test** (`runs/defs-mutants`, `scripts/mutate.py`, spec in
  `indicators/definition-fidelity/mutations.json`): 16 definitions previously judged faithful
  are made wrong by a one-line, type-preserving change (a reversed inequality, `∧` for `∨`, a
  dropped factor, …) in copies of the repositories, keeping their docstrings; all 16 are
  answered `incorrect`, and the 6 unchanged controls `faithful`. Since the docstrings were
  kept, this shows that body/docstring mismatches are caught, not that subtler conceptual
  errors would be.

## Repository layout

| Path | Content |
|---|---|
| `libraries.toml` | The corpus: each library as a set of git sources, with included directories and exclusions |
| `libraries.lock.json` | The commit of each of the 47 source repositories |
| `scripts/fetch.py` | Clones the sources into `repos/` at the pinned commits, and with `--deps` the Mathlib and Batteries versions they pin |
| `scripts/leanscan.py` | Syntactic Lean scanner: finds the theorems and rebuilds the context of each |
| `scripts/sample.py` | Builds the population of each library (theorems or definitions) and draws a seeded uniform sample, or takes a hand-picked list (`--pick`) |
| `scripts/judge.py` | Runs a judge (headless Claude Code) on each sampled theorem, or exports its inputs |
| `scripts/stats.py` | Progress of a judge run |
| `scripts/report.py` | Flag rates, confidence intervals and the list of flags of a judge run |
| `scripts/agreement.py` | Compares two judge runs on the same theorems (test-retest) |
| `scripts/verify.py` | Adversarial second judge that sees the first judge's claims |
| `scripts/indicator.py` | Reads an indicator's `config.toml` |
| `scripts/mutate.py` | Builds and scores a mutation test of a definition indicator |
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
split_field = "proof_uses_it"  # boolean answer field counted among the findings
denominator_excludes = ["not_a_mathematical_object"]  # verdicts left out of the rate
flag_missing_docstring = true  # undocumented declarations get `no_docstring`, no judge
```

`report.py`, `stats.py` and `agreement.py` count the `positive` verdicts; the report lists
the other fields of each finding. A definition indicator runs on a sample drawn with
`sample.py --kind definitions --keep-docstrings`, whose snippets keep the definition's
docstring.

## Reproducing the current experiment

`runs/main` holds 1000 theorems per library (5000 in all), drawn with seed 0 in batches
(`--n 100`, then `--extend` with 100, 100, 100, 300 and 300 per library), which gives exactly
the sample of a single `--n 1000` draw. Coverage of the judge runs:

| Indicator | Label | Theorems |
|---|---|---|
| `unnecessary-hypotheses` | `claude-opus-5-5-high` | all 1000 per library |
| `unnecessary-hypotheses` | `rejudge-claude-opus-5-5-high` (blind second run) | the first 300 per library |
| `duplicates-mathlib` | `claude-opus-5-5-high` | all 1000 per library, Mathlib excepted |

`runs/defs1` holds 1000 definitions per library, drawn with seed 1 (`--kind definitions
--keep-docstrings --n 100`, then `--extend --n 900`), all judged for `definition-fidelity`
(label `claude-opus-5-5-high`). To reproduce it, replace `--run main` by `--run defs1` and
use `--indicator definition-fidelity` below; the sample check is
`python3 scripts/sample.py --run check --kind definitions --keep-docstrings --n 1000 --seed 1`.

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

Under `runs/defs1/definition-fidelity/claude-opus-5-5-high/`: `results/<id>.json` per
definition, `report.md` (1000 per library) and `report-100.md`. The two checks of this judge
are `runs/defs-sensitivity/` and `runs/defs-mutants/` (with `key.json`, saying which samples
are mutants); `python3 scripts/mutate.py --spec indicators/definition-fidelity/mutations.json
--run defs-mutants` rebuilds the mutated copies under `repos/work/` and `--score` scores the
run.

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

  For `definition-fidelity`, every `def`, `abbrev`, `structure`, `class` and
  `irreducible_def`, with the same exclusions: 37,545 in Mathlib, 23,974 in Tau Ceti, 78,295
  in Lean Pool, 79,590 in FLT and 3,884 in Formal Frontier.

- **Mathlib**: `Mathlib/` without `Tactic`, `Util`, `Lean`, `Testing`, `Deprecated`.
- **Formal Frontier**: the main `lean_lib` of each of the 43 library repositories of the
  GitHub organisation (not `pod`, not the Sutherland drafts, not the Test/Examples
  libraries).
- **FLT**: `P2M/Sol`, `P2M/Derive`, `Definitions`. The `Theorems/Thm_*.lean` wrappers are
  skipped because each restates a `solution` theorem of `P2M/Sol` and delegates its proof to
  it. About 93% of the population are helper lemmas of the `P2M/Sol` proofs.
- **Everywhere**: `*/Certificates/*` is excluded (about 81K generated numerical checks in
  Lean Pool, which would otherwise be 22% of its sample).
- **Sampling** is uniform over declarations within each library, so larger projects and
  files weigh in proportion to their number of declarations. Each index is drawn uniformly
  and redrawn if already taken, so a longer draw starts with the shorter one and samples
  can be extended (`--extend`).
- **Snippet.** Each sampled theorem is shown with the enclosing `namespace`/`section`
  commands and the `variable`, `open`, `universe`, `include`, `omit`, `set_option`, local
  attribute/instance and notation commands in effect, then the theorem and its proof, with
  its docstring removed. The judge can read the library's source (docstring included),
  Mathlib and Lean core: for `unnecessary-hypotheses` the pinned Mathlib master commit, for
  `duplicates-mathlib` the Mathlib and Batteries versions each library depends on.

## Subscription-funded library expansion

The completed subscription window expanded **repeated proof machinery** under Sonnet 5.5
at high effort to 372 reviewed files each from Mathlib, Tau Ceti, Formal Frontier,
Lean Pool, FLT and OpenAI Math. The
[library comparison](runs/library-quality-scale-2026-10-26/library-comparison.md)
includes existing first-pass judgments; new sessions skip those targets. Source
selection extends the original seed-zero SHA256 file ordering to 500 files per library;
the window ended before the queue was exhausted. The same run expanded concept
reinvention and simp interface, now retained only in the comparison's appendix and
marked **not ready for use**. See the [source review](runs/library-quality-scale-2026-10-26/sample-review-2026-10-27.json).

`scripts/subscription_audits.py` uses only the `lean-fro` OAuth credential and refuses
new work if extra usage is enabled. It pauses near either quota limit, can resume
after the session reset, and stops at the original weekly reset on 2026-10-27 at
05:00 UTC. Concurrency increases gradually in the absence of rate limits; a rate limit
reduces concurrency and pauses admissions. It never switches to another account or
uses an API key. Costs in the comparison reports remain API equivalents; these
sessions consume the subscription. Reports refresh every five minutes, and final
results are verified and pushed when the window finishes or weekly quota is used.

## AxiomMath CFSG pilot

The [CFSG pilot](runs/cfsg-pilot-2026-10-27/library-comparison.md) pins
`AxiomMath/CFSG` at `5f8042b343bddcb64d288f3e34a6831f12ca05b4`. Its full tree contains
229,089 Lean files; 194,203 candidate files lie under `CFSG/` after excluding certificate
directories. The [source census](runs/cfsg-pilot-2026-10-27/source-census.json) records
these counts. The pilot selects 2,000 eligible whole files using the existing seed-zero
sampling protocol, then judges the first 30 against repeated proof machinery using
Sonnet 5.5 high. These join that audit's library comparison as a new corpus, not a repeat.

All Lean source files are available to the judge, together with every pinned dependency,
including Tau Ceti, Mathlib and Lean core. Non-Lean certificate payloads and documentation
are omitted from the checkout. No Lean code is built or executed. The pilot uses one
lean-fro subscription session, refuses extra usage, and has a $20 API-equivalent ceiling.
Fetch the pinned sources with `python3 scripts/fetch_cfsg.py`. Run
`python3 scripts/cfsg_pilot.py --prepare-only` to prepare, or omit that option to
resume the pilot. The pilot and publication monitor have service templates in `scripts/`.

The [two theorem audits](runs/cfsg-pilot-2026-10-27/theorems/library-comparison.md)
use a separate fixed selection of 2,000 targets drawn uniformly from 1,363,165 eligible
public theorems and lemmas. Sonnet 5.5 high judges the same first 30 for unnecessary
hypotheses and Mathlib duplication, alternating between audits with one session.
The existing theorem protocols are unchanged: hypotheses checks use current-master
Mathlib frozen at preparation, and duplication uses CFSG's pinned Mathlib. Both also
have access to pinned Tau Ceti and the other dependencies. Results join the main
library comparisons, including the combined theorem summary, with costs and intervals.
Run `python3 scripts/cfsg_theorem_audits.py --prepare-only` to prepare, or omit the
option to resume. This pilot has its own $20 API-equivalent ceiling, subscription-only
billing, and worker/publication service templates in `scripts/`.

The [300-target expansion](runs/cfsg-pilot-2026-10-27/scale-300/progress.md) continues
all three CFSG audits with targets 31–300 from those fixed selections. It preserves
the original manifests and judgments and adds each continuation to the same first
pass in the main reports. Run `python3 scripts/cfsg_scale.py file` and
`python3 scripts/cfsg_scale.py theorem` (one session each); add `--prepare-only` to
prepare without judging. The file and theorem workers have separate subscription-only
API-equivalent ceilings of $60 and $50. A publication monitor verifies and pushes
progress every five minutes. Service templates are `scripts/cfsg-scale-*.service`.

The CFSG and OpenAI continuation service templates now use `scripts/sonnet_scale_control.py`:
two isolated judge processes per worker, six sessions total, with starts shared and
spaced five seconds apart. A shared quota check is cached for five minutes; failed
checks retry without admitting new inference or discarding accepted judgments.
Inference 429s and overage rejections stop admission across all three workers.
The saved prompts, source snapshots, selections, validators and spending ceilings
are unchanged; each continuation records its controller hash and runtime settings
in `runtime-control.json`.

## Repeated proof machinery validation

The [validation run](runs/repeated-machinery-validation-2026-10-27/validation-report.md)
checks another 20 flagged and 10 unflagged files per library under Sonnet 5.5 high,
using the lean-fro subscription with two sessions. It excludes the earlier manual
sample. Candidate checks attempt to refute each original finding; discovery tasks
look for missed findings. Source evidence, proposed shared lemmas and rewritten uses
are required. This is a separate conditional check, not another first pass or compiled
verification, and its judgments do not change the main flag counts.

Prepare with `python3 scripts/validate_repeated_machinery.py --prepare-only`; resume
with `python3 scripts/validate_repeated_machinery.py --jobs 2`. The runner preserves
attempt output, checks subscription quotas every minute, stops admissions on a rejected
rate limit and caps API-equivalent inference at $50. Actual API charges are zero under
the subscription; extra usage is refused. A separate monitor verifies and publishes
progress every five minutes, without making inference requests. Service templates are
`scripts/machinery-validation.service` and `scripts/machinery-validation-monitor.service`.
Expansion from 372 to 500 files per library remains conditional on reviewing this check.

## DeepSeek pilot

The matched eight-audit pilot uses DeepSeek V4.1 Flash via OpenRouter on InferenceNet FP8,
with twelve independent sessions sharing a $20 inference cap. It selects 100 theorems per library for each
of the two theorem audits and 10 files per library for each of the six file audits:
1,440 judgments. Selection, launch, status and billed-cost budget are saved under
`runs/deepseek-pilot-2026-10-21/`; results join the existing audit reports.

Resume with `python3 scripts/deepseek_pilot.py --jobs 12` (up to 16 sessions). The runner verifies the saved protocol
and rejects invalid judgments. API requests use a shared adaptive gap recorded in the budget ledger;
HTTP 429 doubles the spacing and triggers an increasing cooldown. It exposes only
Read, Grep and Glob source tools. Interrupted sessions resume from saved responses
and source-tool results. Transient network/provider errors retry the same request
with a shared pause; unfinished targets receive priority on recovery. A final JSON phase follows at most 32 source-inspection turns.
Costs come from each response's billed amount; provider fallbacks are disabled.
The report monitor checks worker health every five minutes and permits at most two
automatic restarts after a cooldown. Invalid evidence remains rejected; exhausted
targets remain unanswered while other selected targets continue.

## Costs

The `cost_usd` fields are what the same tokens would cost at API rates, as reported by
`claude -p`; with a Claude subscription, the runs draw on its usage quota instead. The first
`unnecessary-hypotheses` run cost about $374 for 5000 theorems (a median of 3 agent turns
per theorem), its second run $108 for 1500; the `duplicates-mathlib` run about $216 for 4000;
the `definition-fidelity` run about $336 for the 4000 definitions it judged (FLT's are
flagged by rule).

Verify the DeepSeek run without making API calls:

```sh
python3 scripts/verify_deepseek_pilot.py --require-complete
```

This checks the fixed selection, pinned source commits, prompt/schema hashes, accepted
verdicts against saved API responses, file evidence, generation IDs and billed costs.
It exits unsuccessfully until every selected target has an accepted judgment. Raw local
session transcripts are required for this check; they are excluded from Git.

The local monitor is installed as the enabled user service
`lean-quality-deepseek-monitor.service` (template: `scripts/deepseek-monitor.service`).
It restarts after failures and starts when the user's service manager starts after a
reboot. This machine denies enabling user lingering, so startup before login requires
an administrator; the existing account session runs it normally. Worker identities
include boot IDs and process start times to avoid mistaking a reused PID for a judge.
