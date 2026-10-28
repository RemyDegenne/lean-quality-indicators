# Running the experiments

How to fetch the corpus, draw samples, run the judges and rebuild the reports. What is
measured and how is described in the [README](README.md).

## Requirements

- Python ≥ 3.11 and git. The core pipeline (fetching, sampling, judging with Claude Code,
  reports) uses only the standard library.
- About 1.5 GB of disk for the clones, plus 0.8 GB for the pinned Mathlib and Batteries
  versions (`fetch.py --deps`, needed by indicators with `mathlib = "pinned"`).
- To run the Claude judges: [Claude Code](https://claude.com/claude-code), logged in (the
  runner calls `claude -p`; no API key needed with a subscription). The runner passes
  `--restricted`, so it needs a version that supports it (tested with 2.1.304).
- To run the Sol and Luna judges: Codex CLI (tested with 0.163.0) and ripgrep.
- Optional: the Lean toolchains the libraries use, installed with
  [elan](https://github.com/leanprover/elan), so the judges can read the Lean core sources:
  `elan toolchain install leanprover/lean4:v4.36.0-rc1` (Mathlib, Tau Ceti), `v4.35.0-rc3`
  (Lean Pool), `v4.34.0-rc2` (Formal Frontier), `v4.33.1` (FLT). Nothing is built. Keep the
  same toolchains installed throughout a run.
- To render the whitepaper PDF: markdown-it-py, XeLaTeX and Poppler.

Unit tests: `python3 -m unittest discover -s scripts -v`.

## Theorem and definition indicators

1. **Corpus.** `python3 scripts/fetch.py` clones every source at its pinned commit.
   `python3 scripts/fetch.py --update` moves every source to its latest commit and rewrites
   the lock instead (a new corpus, so start a new run). `--deps` also clones, under
   `repos/deps/`, the Mathlib and Batteries commits that each source pins in its
   `lake-manifest.json`. To add a library, add it to `libraries.toml` and run `fetch.py`.
2. **Sample.** `python3 scripts/sample.py --run NAME --n N --seed S` draws N theorems per
   library into `runs/NAME/`. `--extend --n M` adds M more per library to an existing run,
   from the same seeded draw, so the union is exactly what one draw of N + M would give.
   `--kind definitions --keep-docstrings` samples definitions instead, keeping their
   docstrings in the snippets. `--pick` takes a hand-picked list. `--population-only`
   prints the population sizes; `--diagnose` also lists column-0 words the scanner does not
   recognise as commands.
3. **Judge.** `python3 scripts/judge.py --run NAME --jobs 8` judges every sample with the
   `unnecessary-hypotheses` indicator (`--indicator NAME` for another). Options: `--model`,
   `--effort`, `--backend codex` (see [below](#codex-judges-sol-and-luna)), `--label`
   (results go to `runs/NAME/<indicator>/<label>/results/`, default label
   `<model>-<effort>`), `--libs`, `--ids`, `--limit` (per library), `--claude PATH` (Claude
   Code executable). Rerunning the same command resumes: judged samples are skipped and
   failed calls retried. `python3 scripts/stats.py --run NAME [--indicator NAME] --label
   LABEL` shows progress.
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
the other fields of each finding.

## Reproducing `runs/main` and `runs/defs1`

`runs/main` holds 1000 theorems per library (5000 in all), drawn with seed 0 in batches
(`--n 100`, then `--extend` with 100, 100, 100, 300 and 300 per library), which gives exactly
the sample of a single `--n 1000` draw. Its judge runs:

| Indicator | Label | Theorems |
|---|---|---|
| `unnecessary-hypotheses` | `claude-opus-5-5-high` | all 1000 per library |
| `unnecessary-hypotheses` | `rejudge-claude-opus-5-5-high` (blind second run) | the first 300 per library |
| `unnecessary-hypotheses` | `claude-sonnet-5-5-high`, `gpt-6.1-sol-high`, `gpt-6-luna-high`, and their `-repeat-2` second passes | the first 300 per library |
| `unnecessary-hypotheses` | `deepseek-v4.1-flash-1017-openrouter-high` | the DeepSeek pilot selection |
| `duplicates-mathlib` | `claude-opus-5-5-high` | all 1000 per library, Mathlib excepted |
| `duplicates-mathlib-inclusive` | `claude-sonnet-5-5-high`, `gpt-6.1-sol-high`, `gpt-6-luna-high` | all 1000 per library |
| `duplicates-mathlib-inclusive` | `deepseek-v4.1-flash-1017-openrouter-high` | the DeepSeek pilot selection |

`runs/defs1` holds 1000 definitions per library, drawn with seed 1 (`--kind definitions
--keep-docstrings --n 100`, then `--extend --n 900`), all judged for `definition-fidelity`
(label `claude-opus-5-5-high`). To reproduce it, replace `--run main` by `--run defs1` and
use `--indicator definition-fidelity` below; the sample check is
`python3 scripts/sample.py --run check --kind definitions --keep-docstrings --n 1000 --seed 1`.

1. Clone this repository and fetch the corpus at the pinned commits, with the pinned Mathlib
   and Batteries versions:

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
   duplicates-mathlib-inclusive` for the duplicates indicator, and `--limit 400` to judge
   only the first 400 per library).

   - **With Claude Code or Codex**, using our runner:

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

LLM verdicts vary between runs even with the same model and prompt (see the
[test-retest](runs/main/unnecessary-hypotheses/rejudge-claude-opus-5-5-high/agreement-full.md)).
A reproduction should be read as matching rates and high agreement, not identical verdicts.

### Files of `runs/main` and `runs/defs1`

- `runs/main/samples.jsonl`: the 5000 sampled theorems (library, repository, commit, path,
  lines, name, GitHub link); `samples/<lib>/<id>.lean`: the snippet each judge received;
  `run.json`: seed, population sizes, commits, batches.
- `unnecessary-hypotheses/claude-opus-5-5-high/`: first Opus run. `results/<id>.json` per
  theorem; `report.md` (1000 per library), `report-400.md`, `report-batch3.md`,
  `report-batch2.md`, `report-batch1.md` (400, 300, 200, 100 per library).
- `unnecessary-hypotheses/claude-opus-5-5-high/verify/claude-opus-5-5-high/`: adversarial
  verification of the flags among the first 300 per library (kept for the record).
- `unnecessary-hypotheses/rejudge-claude-opus-5-5-high/`: blind second run on the first 300
  per library. `report.md`; `agreement-full.md` (comparison with the first run, every
  disagreement); `agreement.md` (the first run's flags plus as many random non-flags,
  selected in `rejudge-ids.json`).
- `unnecessary-hypotheses/model-comparison.md` and `audit-comparison.md`: all judges on
  this indicator.
- `duplicates-mathlib/claude-opus-5-5-high/`: `results/<id>.json` per theorem; `report.md`
  (1000 per library), `report-400.md`, `report-700.md`. The first 10 theorems per library
  were judged in the test of the final prompt, the rest in the full run (the runner judges
  the libraries in turn, so progress is even across them).
- `duplicates-mathlib-inclusive/`: the later judges, with `model-comparison.md` and
  `audit-comparison.md`.

Under `runs/defs1/definition-fidelity/claude-opus-5-5-high/`: `results/<id>.json` per
definition, `report.md` (1000 per library) and `report-100.md`. The two checks of this judge
are `runs/defs-sensitivity/` and `runs/defs-mutants/` (with `key.json`, saying which samples
are mutants); `python3 scripts/mutate.py --spec indicators/definition-fidelity/mutations.json
--run defs-mutants` rebuilds the mutated copies under `repos/work/` and `--score` scores the
run.

## Codex judges (Sol and Luna)

The Codex backend sits beside the Claude Code backend. The comparison uses **the original
first 300 samples per library** of `runs/main`, not all 1000. No sampling or corpus update
is needed. Fetch exactly the locked source commits:

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
halves the concurrency limit, and sets a five-minute cooldown shared by both models.
Internal Codex reconnect errors are checked even when a later retry might have succeeded.
Sonnet runs two sessions separately. Without the wrapper, `--jobs` counts independent
sessions for each model. Use saved Codex and Claude Code login credentials. The guard state
and events are stored in ignored `codex-rate-guard-*.log` files beside the results.

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
when the benchmark's completion marker appears. The
[2026-10-20 tuning measurements](runs/main/unnecessary-hypotheses/rate-tuning.json)
selected nine shared Sol/Luna sessions with three-second start spacing.

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

## Duplicates of Mathlib, including Mathlib

`duplicates-mathlib-inclusive` is an explicitly modified replication of
`duplicates-mathlib`: it adds the self-match and circularity exclusions and a Mathlib arm.
Judges must inspect candidate proofs to establish independence. The reproduction uses the
same 1000 samples per library, once each for Sol 6.1, Luna 6 and Sonnet 5.5, all at high
effort: 15,000 judgments.

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
Opus has no Mathlib baseline. A success marker is written only when every selected
judgment and report is complete. Resuming skips saved verdicts.

## File audits

[audits/file-quality-v1/README.md](audits/file-quality-v1/README.md) describes the file
sample, the protocol and the runners (`scripts/file_audits.py`,
`scripts/repeated_machinery_audit.py`, `scripts/reproduce_file_audits.py`). The pilot is
`runs/file-quality-pilot-2026-10-21/`: ten files each from Mathlib, Tau Ceti and Lean Pool,
with every rubric on the same thirty files. Samples, protocol snapshots and model results
are separated so coverage and models can be expanded without replacing the pilot data.
Every positive of the repeated-machinery pilot has an
[individual source review](runs/file-quality-pilot-2026-10-21/reviews/repeated-machinery-2026-10-21.md).

### Subscription-funded expansion

`runs/library-quality-scale-2026-10-26/` expanded repeated proof machinery (and the two
appendix audits) under Sonnet 5.5 at high effort to 372 reviewed files each from Mathlib,
Tau Ceti, Formal Frontier, Lean Pool, FLT and OpenAI Math. Its library comparison includes
existing first-pass judgments; new sessions skip those targets. Source selection extends
the original seed-zero SHA256 file ordering to 500 files per library; the subscription
window ended before the queue was exhausted.

`scripts/subscription_audits.py` uses only the `lean-fro` OAuth credential and refuses
new work if extra usage is enabled. It pauses near either quota limit, can resume
after the session reset, and stops at the weekly reset it was configured for
(2026-10-27, 05:00 UTC). Concurrency increases gradually in the absence of rate limits; a
rate limit reduces concurrency and pauses admissions. It never switches to another account
or uses an API key. Costs in the comparison reports remain API equivalents; these sessions
consume the subscription.

## OpenAI Math

`runs/openai-math-2026-10-21/` has fixed selections of 2,000 theorem targets and 2,000
whole files from `lean/OAI/`. Opus, Sol, Sonnet and Luna judged the first 100 targets on
each audit, with two Sol sessions, one session each for the other models, and the shared
Codex rate guard. All 42 pinned dependencies are available as read-only sources. Resume
with `python3 scripts/corpus_pilot.py judge --model Sol --jobs 2`.

Sonnet's unnecessary-hypothesis and Mathlib-duplication audits continue to 300 targets,
adding targets 101–300 from the same frozen theorem selection (`scale-300/theorems/`); the
first 100 judgments are preserved and join the same first pass in the main reports. Run
`python3 scripts/openai_scale.py --prepare-only` to prepare, or omit the option to resume
with one Sonnet 5.5 high session on the lean-fro subscription. The continuation has a $40
API-equivalent ceiling, refuses API-key billing and extra usage, and pauses on rate-limit
rejection. Worker and publication templates are `scripts/openai-scale*.service`.

## CFSG (AxiomMath)

Fetch the pinned sources with `python3 scripts/fetch_cfsg.py`. All Lean source files are
available to the judge, together with every pinned dependency, including Tau Ceti, Mathlib
and Lean core. Non-Lean certificate payloads and documentation are omitted from the
checkout. No Lean code is built or executed.

- **Files.** The pilot selects 2,000 eligible whole files using the existing seed-zero
  sampling protocol, then judges the first 30 against repeated proof machinery using
  Sonnet 5.5 high. Run `python3 scripts/cfsg_pilot.py --prepare-only` to prepare, or omit
  that option to resume. One lean-fro subscription session, extra usage refused, $20
  API-equivalent ceiling.
- **Theorems.** A separate fixed selection of 2,000 targets drawn uniformly from the
  eligible public theorems and lemmas. Sonnet 5.5 high judges the first 30 for unnecessary
  hypotheses and Mathlib duplication, alternating between audits with one session. The
  theorem protocols are unchanged: hypotheses checks use current-master Mathlib frozen at
  preparation, and duplication uses CFSG's pinned Mathlib. Run
  `python3 scripts/cfsg_theorem_audits.py --prepare-only` to prepare, or omit the option to
  resume. Own $20 API-equivalent ceiling, subscription-only billing.
- **300-target expansion** (`scale-300/`). Continues all three audits with targets 31–300
  from those fixed selections, preserving the original manifests and judgments. Run
  `python3 scripts/cfsg_scale.py file` and `python3 scripts/cfsg_scale.py theorem` (one
  session each); add `--prepare-only` to prepare without judging. The file and theorem
  workers have separate subscription-only API-equivalent ceilings of $60 and $50.

The CFSG and OpenAI continuation service templates use `scripts/sonnet_scale_control.py`:
two isolated judge processes per worker, six sessions total, with starts shared and
spaced five seconds apart. A shared quota check is cached for five minutes; failed
checks retry without admitting new inference or discarding accepted judgments.
Inference 429s and overage rejections stop admission across all three workers.
The saved prompts, source snapshots, selections, validators and spending ceilings
are unchanged; each continuation records its controller hash and runtime settings
in `runtime-control.json`. Service templates for the workers and publication monitors
are `scripts/cfsg-*.service`.

## Repeated proof machinery validation

`runs/repeated-machinery-validation-2026-10-27/` checks another 20 flagged and 10
unflagged files per library under Sonnet 5.5 high, using the lean-fro subscription with
two sessions. It excludes the earlier manual sample. Candidate checks attempt to refute
each original finding; discovery tasks look for missed findings. Source evidence, proposed
shared lemmas and rewritten uses are required. This is a separate conditional check, not
another first pass or compiled verification, and its judgments do not change the main
flag counts.

Prepare with `python3 scripts/validate_repeated_machinery.py --prepare-only`; resume
with `python3 scripts/validate_repeated_machinery.py --jobs 2`. The runner preserves
attempt output, checks subscription quotas every minute, stops admissions on a rejected
rate limit and caps API-equivalent inference at $50. Extra usage is refused. A separate
monitor verifies and publishes progress every five minutes, without making inference
requests. Service templates are `scripts/machinery-validation.service` and
`scripts/machinery-validation-monitor.service`.

## DeepSeek pilot

The matched eight-audit pilot uses DeepSeek V4.1 Flash via OpenRouter on InferenceNet FP8,
with twelve independent sessions sharing a $20 inference cap. It selects 100 theorems per
library for each of the two theorem audits and 10 files per library for each of the six
file audits: 1,440 judgments. Selection, launch, status and billed-cost budget are saved
under `runs/deepseek-pilot-2026-10-21/`; results join the existing audit runs.
[AUDIT_METHODS.md](AUDIT_METHODS.md) records the provider history and pacing changes.

Resume with `python3 scripts/deepseek_pilot.py --jobs 12` (up to 16 sessions). The runner
verifies the saved protocol and rejects invalid judgments. API requests use a shared
adaptive gap recorded in the budget ledger; HTTP 429 doubles the spacing and triggers an
increasing cooldown. It exposes only Read, Grep and Glob source tools. Interrupted sessions
resume from saved responses and source-tool results. Transient network/provider errors
retry the same request with a shared pause; unfinished targets receive priority on
recovery. A final JSON phase follows at most 32 source-inspection turns. Costs come from
each response's billed amount; provider fallbacks are disabled.

Verify the DeepSeek run without making API calls:

```sh
python3 scripts/verify_deepseek_pilot.py --require-complete
```

This checks the fixed selection, pinned source commits, prompt/schema hashes, accepted
verdicts against saved API responses, file evidence, generation IDs and billed costs.
It exits unsuccessfully until every selected target has an accepted judgment. Raw local
session transcripts are required for this check; they are excluded from Git.

The report monitor (template: `scripts/deepseek-monitor.service`) checks worker health
every five minutes and permits at most two automatic restarts after a cooldown. Invalid
evidence remains rejected; exhausted targets remain unanswered while other selected
targets continue. Worker identities include boot IDs and process start times to avoid
mistaking a reused PID for a judge.

## Reports and monitors

- `python3 scripts/audit_dashboard.py` regenerates [AUDIT_RESULTS.md](AUDIT_RESULTS.md),
  [AUDIT_RESULTS.json](AUDIT_RESULTS.json), [AUDIT_APPENDIX.md](AUDIT_APPENDIX.md) and the
  per-audit comparisons. Which audits go to the appendix is set in
  `scripts/audit_reporting.py`. `scripts/api_costs.py` builds the
  [cost summary](runs/main/api-equivalent-costs.md) from the
  [frozen rates](pricing/api-rates-2026-10-21.json).
- `scripts/watch_audit_reports.py` refreshes the reports every five minutes while runs are
  in progress.
- `scripts/watch_whitepaper.py` waits for every selected target in the Sonnet
  continuations to have an accepted judgment. It then verifies the results, refreshes
  the whitepaper's Sonnet cells and coverage text while preserving other edits, and
  regenerates and pushes the Markdown and two-page PDF. The service template is
  `scripts/whitepaper-monitor.service`; its log is `runs/main/whitepaper-monitor.log`.
  Rendering uses `scripts/render_whitepaper.py`. A paused or failed target does not count
  as completion.
