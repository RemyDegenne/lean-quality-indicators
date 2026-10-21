# concept-reinvention

Generated 2026-10-21T05:09:12+00:00.

Targets are distinct selected source files/theorems, not findings. A judgment is flagged when it reports at least one finding. Passes show completed / planned; an unfinished pass is included in the judgment and flag counts. The flag-rate interval uses the first pass only, with Wilson 95% limits; repeated judgments are not treated as independent targets.

Correlations are Pearson r on binary flag decisions (the phi coefficient). Cross-model cells use matching completed targets from each model's first pass. Diagonal cells compare the first two independent passes, where available. Intervals are paired-target percentile bootstrap 95% intervals, stratified by library (2,000 draws, fixed seeds). A dash means no estimate/interval: insufficient matches, constant decisions, a boundary estimate or too many degenerate resamples. The intervals describe sampling uncertainty, not correctness against ground truth. First-pass and repeat-pass matches need not have the same n.

Expenditure cells are **$X / $Y** in USD at API-equivalent rates. X is recorded expenditure to date, including retained retry usage. Y estimates a single pass at the largest completed pass's target count, using this model's expenditure per completed judgment across its passes. Y is an extrapolation when coverage is smaller; it does not assume equal token use or prices across models. Deleted or overwritten usage cannot be reconstructed. See the [cost methods and rates](../../main/api-equivalent-costs.md).

Not-applicable judgments count as unflagged. Partial and not-applicable counts are recorded below. Sol and Opus have no file-audit runs.

## All libraries

Full-pass cost reference: **30 targets**, the largest completed pass in this group.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Luna | 30 | 0/1 | 15/30 | 0 | 0 | 0.0% [0.0%, 20.4%] | $0.08 / $0.16 |
| Sonnet | 30 | 1/1 | 30/30 | 6 | 6 | 20.0% [9.5%, 37.3%] | $2.19 / $2.19 |
| GLM | 30 | 0/1 | 0/30 | 0 | 0 | — | $0.00 / — |

### Correlation matrix

Cells: r [95% CI]; n is the number of matched targets.

| Model | Luna | Sonnet | GLM |
|---|---:|---:|---:|
| Luna | — | —; n=15 | — |
| Sonnet | —; n=15 | — | — |
| GLM | — | — | — |

Coverage annotations: Luna: 0 partial, 0 not applicable; Sonnet: 0 partial, 5 not applicable; GLM: 0 partial, 0 not applicable.

## Mathlib

Full-pass cost reference: **10 targets**, the largest completed pass in this group.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Luna | 10 | 0/1 | 5/10 | 0 | 0 | 0.0% [0.0%, 43.4%] | $0.02 / $0.04 |
| Sonnet | 10 | 1/1 | 10/10 | 2 | 2 | 20.0% [5.7%, 51.0%] | $0.71 / $0.71 |
| GLM | 10 | 0/1 | 0/10 | 0 | 0 | — | $0.00 / — |

### Correlation matrix

Cells: r [95% CI]; n is the number of matched targets.

| Model | Luna | Sonnet | GLM |
|---|---:|---:|---:|
| Luna | — | —; n=5 | — |
| Sonnet | —; n=5 | — | — |
| GLM | — | — | — |

Coverage annotations: Luna: 0 partial, 0 not applicable; Sonnet: 0 partial, 1 not applicable; GLM: 0 partial, 0 not applicable.

## Tau Ceti

Full-pass cost reference: **10 targets**, the largest completed pass in this group.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Luna | 10 | 0/1 | 5/10 | 0 | 0 | 0.0% [0.0%, 43.4%] | $0.02 / $0.05 |
| Sonnet | 10 | 1/1 | 10/10 | 0 | 0 | 0.0% [0.0%, 27.8%] | $0.39 / $0.39 |
| GLM | 10 | 0/1 | 0/10 | 0 | 0 | — | $0.00 / — |

### Correlation matrix

Cells: r [95% CI]; n is the number of matched targets.

| Model | Luna | Sonnet | GLM |
|---|---:|---:|---:|
| Luna | — | —; n=5 | — |
| Sonnet | —; n=5 | — | — |
| GLM | — | — | — |

Coverage annotations: Luna: 0 partial, 0 not applicable; Sonnet: 0 partial, 3 not applicable; GLM: 0 partial, 0 not applicable.

## Lean Pool

Full-pass cost reference: **10 targets**, the largest completed pass in this group.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Luna | 10 | 0/1 | 5/10 | 0 | 0 | 0.0% [0.0%, 43.4%] | $0.04 / $0.08 |
| Sonnet | 10 | 1/1 | 10/10 | 4 | 4 | 40.0% [16.8%, 68.7%] | $1.10 / $1.10 |
| GLM | 10 | 0/1 | 0/10 | 0 | 0 | — | $0.00 / — |

### Correlation matrix

Cells: r [95% CI]; n is the number of matched targets.

| Model | Luna | Sonnet | GLM |
|---|---:|---:|---:|
| Luna | — | —; n=5 | — |
| Sonnet | —; n=5 | — | — |
| GLM | — | — | — |

Coverage annotations: Luna: 0 partial, 0 not applicable; Sonnet: 0 partial, 1 not applicable; GLM: 0 partial, 0 not applicable.
