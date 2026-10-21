# File quality audits, version 1

The concept rubric protects useful named API and requires a competing definition with a
concrete cost. Its thirty Sonnet reviews are complete. To run it alone on the existing
thirty-file sample, with separate reports:

```sh
python3 -u scripts/reinvention_audit.py --run file-quality-pilot-2026-10-21 \
  --files-per-library 10 --model claude-sonnet-5-5 \
  --label claude-sonnet-5-5-high-concept --jobs 2
```

The repeated-machinery rubric requires a shared lemma, a proof sketch and rewritten
existing uses showing an overall improvement. Run it on the same sample, with a separate
thirty-review report:

```sh
python3 -u scripts/repeated_machinery_audit.py --run file-quality-pilot-2026-10-21 \
  --files-per-library 10 --model claude-sonnet-5-5 \
  --label claude-sonnet-5-5-high-structure-machinery --jobs 2
```

Four selected audits are being independently reproduced by Luna on the same thirty files:
generality, vacuity/misstatement, simp interface and readable proof simplification.
`scripts/reproduce_file_audits.py` restricts that run and its reports to those four rubrics
(120 reviews). It uses one active session behind the shared Codex guard.

Six independent rubrics review whole files: concepts already present in Mathlib,
statement generality, vacuity or misstatement, simp
interfaces, repeated proof machinery, and readable proof simplification.
The concept rubric applies within Mathlib too. Names, namespaces, module placement and
typeclass instance design are outside this suite.

The pilot uses ten files each from Mathlib, Tau Ceti and Lean Pool, uniformly sampled over
eligible files rather than weighted by theorem count. Candidate paths use the existing
corpus include/exclude rules. Eligibility requires a mathematical declaration keyword at
the start of a command in source with comments and strings masked; this is an approximate
syntactic filter, not Lean elaboration. Private declarations and comments remain visible
because the entire file is the unit of review. No file size cutoff is used.

Every rubric uses exactly the same thirty files. A fresh, isolated Sonnet 5.5 session at
high effort reviews one file against one rubric, for 180 judgments. There are two active
sessions total. Read, Grep and Glob are the only tools; Lean is not executed and source
files are never edited. The judge can read the library's own source, its pinned Mathlib
and Batteries dependencies, and the corresponding Lean core sources. It cannot access
saved judgments. There are at most five findings per file and rubric; coverage and
non-applicability are recorded separately. Quotations and finding line ranges are checked
against the actual allowed sources before results are accepted.

```sh
python3 -u scripts/file_audits.py --run file-quality-pilot-2026-10-21 \
  --files-per-library 10 --model claude-sonnet-5-5 --jobs 2
```

`--prepare-only` samples and snapshots inputs without making model requests. Repeating the
command resumes saved results. Increase `--files-per-library` to extend the same sample
without changing existing file IDs. Change `--model` (and `--backend codex` when appropriate)
to add separately stored model judgments; `--label` can name an independent repeat.
`--rubrics` selects a comma-separated subset. Run only one controller per run and label.
On a failed judgment the runner stops launching new work; inspect the error and resume.

The immutable sampling contract records the corpus and candidate population hashes, seed
and eligibility method. Files are ordered by a hash of the seed, library and path, then
the first eligible files are taken. Sample metadata records source commits, hashes, full
file snapshots and URLs. `protocols/` snapshots each complete prompt, schema and message;
each snapshot must match its rubric, and judgments from different prompts are never
combined. Each rubric/model directory records
runner hashes, CLI version and the history of file selections used as coverage expands.

Results live under `runs/file-quality-pilot-2026-10-21/`:

- `run.json`, `corpus-lock.json`, `samples.jsonl`, `files/`: the frozen file sample.
- `protocols/<rubric>/`: the complete inputs defining each rubric.
- `<rubric>/<model>-<effort>/judge.json` and `results/`: provenance and structured judgments.
- `reports/<model>-<effort>/`: the summary, individual findings, live status and completion marker.

Raw transcripts and operational logs stay local; prompts, snapshots and judgments can be
versioned. Reports count files with findings, completed reviews, partial reviews,
non-applicable reviews and individual findings. They do not claim a theorem defect rate,
exhaustive coverage, verified replacement proofs or independent confirmation. A finding
may legitimately appear under several rubrics.
