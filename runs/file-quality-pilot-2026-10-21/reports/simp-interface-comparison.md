# simp-interface

Generated 2026-10-21T05:09:12+00:00.

Targets are distinct selected source files/theorems, not findings. A judgment is flagged when it reports at least one finding. Passes show completed / planned; an unfinished pass is included in the judgment and flag counts. The flag-rate interval uses the first pass only, with Wilson 95% limits; repeated judgments are not treated as independent targets.

Correlations are Pearson r on binary flag decisions (the phi coefficient). Cross-model cells use matching completed targets from each model's first pass. Diagonal cells compare the first two independent passes, where available. Intervals are paired-target percentile bootstrap 95% intervals, stratified by library (2,000 draws, fixed seeds). A dash means no estimate/interval: insufficient matches, constant decisions, a boundary estimate or too many degenerate resamples. The intervals describe sampling uncertainty, not correctness against ground truth. First-pass and repeat-pass matches need not have the same n.

Expenditure cells are **$X / $Y** in USD at API-equivalent rates. X is recorded expenditure to date, including retained retry usage. Y estimates a single pass at the largest completed pass's target count, using this model's expenditure per completed judgment across its passes. Y is an extrapolation when coverage is smaller; it does not assume equal token use or prices across models. Deleted or overwritten usage cannot be reconstructed. See the [cost methods and rates](../../main/api-equivalent-costs.md).

Not-applicable judgments count as unflagged. Partial and not-applicable counts are recorded below. Sol and Opus have no file-audit runs.

## All libraries

Full-pass cost reference: **30 targets**, the largest completed pass in this group.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Luna | 30 | 0/1 | 18/30 | 4 | 4 | 22.2% [9.0%, 45.2%] | $0.09 / $0.16 |
| Sonnet | 30 | 1/1 | 30/30 | 13 | 13 | 43.3% [27.4%, 60.8%] | $2.39 / $2.39 |
| GLM | 30 | 0/1 | 0/30 | 0 | 0 | — | $0.00 / — |

### Correlation matrix

Cells: r [95% CI]; n is the number of matched targets.

| Model | Luna | Sonnet | GLM |
|---|---:|---:|---:|
| Luna | — | 0.67 [0.40, 1.00]; n=18 | — |
| Sonnet | 0.67 [0.40, 1.00]; n=18 | — | — |
| GLM | — | — | — |

Coverage annotations: Luna: 0 partial, 0 not applicable; Sonnet: 0 partial, 1 not applicable; GLM: 0 partial, 0 not applicable.

## Mathlib

Full-pass cost reference: **10 targets**, the largest completed pass in this group.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Luna | 10 | 0/1 | 6/10 | 1 | 1 | 16.7% [3.0%, 56.4%] | $0.03 / $0.04 |
| Sonnet | 10 | 1/1 | 10/10 | 4 | 4 | 40.0% [16.8%, 68.7%] | $0.68 / $0.68 |
| GLM | 10 | 0/1 | 0/10 | 0 | 0 | — | $0.00 / — |

### Correlation matrix

Cells: r [95% CI]; n is the number of matched targets.

| Model | Luna | Sonnet | GLM |
|---|---:|---:|---:|
| Luna | — | 1.00 [—]; n=6 | — |
| Sonnet | 1.00 [—]; n=6 | — | — |
| GLM | — | — | — |

Coverage annotations: Luna: 0 partial, 0 not applicable; Sonnet: 0 partial, 1 not applicable; GLM: 0 partial, 0 not applicable.

## Tau Ceti

Full-pass cost reference: **10 targets**, the largest completed pass in this group.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Luna | 10 | 0/1 | 6/10 | 0 | 0 | 0.0% [0.0%, 39.0%] | $0.03 / $0.05 |
| Sonnet | 10 | 1/1 | 10/10 | 3 | 3 | 30.0% [10.8%, 60.3%] | $0.68 / $0.68 |
| GLM | 10 | 0/1 | 0/10 | 0 | 0 | — | $0.00 / — |

### Correlation matrix

Cells: r [95% CI]; n is the number of matched targets.

| Model | Luna | Sonnet | GLM |
|---|---:|---:|---:|
| Luna | — | —; n=6 | — |
| Sonnet | —; n=6 | — | — |
| GLM | — | — | — |

Coverage annotations: Luna: 0 partial, 0 not applicable; Sonnet: 0 partial, 0 not applicable; GLM: 0 partial, 0 not applicable.

## Lean Pool

Full-pass cost reference: **10 targets**, the largest completed pass in this group.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Luna | 10 | 0/1 | 6/10 | 3 | 3 | 50.0% [18.8%, 81.2%] | $0.04 / $0.06 |
| Sonnet | 10 | 1/1 | 10/10 | 6 | 6 | 60.0% [31.3%, 83.2%] | $1.04 / $1.04 |
| GLM | 10 | 0/1 | 0/10 | 0 | 0 | — | $0.00 / — |

### Correlation matrix

Cells: r [95% CI]; n is the number of matched targets.

| Model | Luna | Sonnet | GLM |
|---|---:|---:|---:|
| Luna | — | 0.71 [—]; n=6 | — |
| Sonnet | 0.71 [—]; n=6 | — | — |
| GLM | — | — | — |

Coverage annotations: Luna: 0 partial, 0 not applicable; Sonnet: 0 partial, 0 not applicable; GLM: 0 partial, 0 not applicable.
