# duplicates-mathlib-inclusive

Generated 2026-10-21T05:09:11+00:00.

Targets are distinct selected source files/theorems, not findings. A judgment is flagged when it reports at least one finding. Passes show completed / planned; an unfinished pass is included in the judgment and flag counts. The flag-rate interval uses the first pass only, with Wilson 95% limits; repeated judgments are not treated as independent targets.

Correlations are Pearson r on binary flag decisions (the phi coefficient). Cross-model cells use matching completed targets from each model's first pass. Diagonal cells compare the first two independent passes, where available. Intervals are paired-target percentile bootstrap 95% intervals, stratified by library (2,000 draws, fixed seeds). A dash means no estimate/interval: insufficient matches, constant decisions, a boundary estimate or too many degenerate resamples. The intervals describe sampling uncertainty, not correctness against ground truth. First-pass and repeat-pass matches need not have the same n.

Expenditure cells are **$X / $Y** in USD at API-equivalent rates. X is recorded expenditure to date, including retained retry usage. Y estimates a single pass at the largest completed pass's target count, using this model's expenditure per completed judgment across its passes. Y is an extrapolation when coverage is smaller; it does not assume equal token use or prices across models. Deleted or overwritten usage cannot be reconstructed. See the [cost methods and rates](../api-equivalent-costs.md).

Opus is the original four-library baseline, without Mathlib targets and with the earlier prompt. Correlations involving Opus therefore also reflect the prompt difference.

## All libraries

Full-pass cost reference: **5000 targets**, the largest completed pass in this group.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 4000 | 1/1 | 4000/4000 | 301 | 301 | 7.5% [6.7%, 8.4%] | $216.29 / $270.36 |
| Sol | 5000 | 1/1 | 5000/5000 | 1447 | 1447 | 28.9% [27.7%, 30.2%] | $319.51 / $319.51 |
| Luna | 5000 | 1/1 | 5000/5000 | 1352 | 1352 | 27.0% [25.8%, 28.3%] | $16.00 / $16.00 |
| Sonnet | 5000 | 1/1 | 5000/5000 | 519 | 519 | 10.4% [9.6%, 11.3%] | $124.97 / $124.97 |
| GLM | 50 | 0/1 | 4/50 | 2 | 2 | 50.0% [15.0%, 85.0%] | $0.10 / $122.62 |

### Correlation matrix

Cells: r [95% CI]; n is the number of matched targets.

| Model | Opus | Sol | Luna | Sonnet | GLM |
|---|---:|---:|---:|---:|---:|
| Opus | — | 0.57 [0.54, 0.60]; n=4000 | 0.54 [0.51, 0.57]; n=4000 | 0.74 [0.70, 0.78]; n=4000 | —; n=3 |
| Sol | 0.57 [0.54, 0.60]; n=4000 | — | 0.69 [0.67, 0.71]; n=5000 | 0.48 [0.46, 0.51]; n=5000 | 0.58 [0.58, 0.58]; n=4 |
| Luna | 0.54 [0.51, 0.57]; n=4000 | 0.69 [0.67, 0.71]; n=5000 | — | 0.50 [0.48, 0.52]; n=5000 | 0.58 [0.58, 0.58]; n=4 |
| Sonnet | 0.74 [0.70, 0.78]; n=4000 | 0.48 [0.46, 0.51]; n=5000 | 0.50 [0.48, 0.52]; n=5000 | — | —; n=4 |
| GLM | —; n=3 | 0.58 [0.58, 0.58]; n=4 | 0.58 [0.58, 0.58]; n=4 | —; n=4 | — |

## Mathlib

Full-pass cost reference: **1000 targets**, the largest completed pass in this group.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sol | 1000 | 1/1 | 1000/1000 | 689 | 689 | 68.9% [66.0%, 71.7%] | $54.38 / $54.38 |
| Luna | 1000 | 1/1 | 1000/1000 | 596 | 596 | 59.6% [56.5%, 62.6%] | $2.71 / $2.71 |
| Sonnet | 1000 | 1/1 | 1000/1000 | 263 | 263 | 26.3% [23.7%, 29.1%] | $30.36 / $30.36 |
| GLM | 10 | 0/1 | 1/10 | 1 | 1 | 100.0% [20.7%, 100.0%] | $0.02 / $19.09 |

### Correlation matrix

Cells: r [95% CI]; n is the number of matched targets.

| Model | Opus | Sol | Luna | Sonnet | GLM |
|---|---:|---:|---:|---:|---:|
| Opus | — | — | — | — | — |
| Sol | — | — | 0.56 [0.51, 0.61]; n=1000 | 0.35 [0.31, 0.39]; n=1000 | —; n=1 |
| Luna | — | 0.56 [0.51, 0.61]; n=1000 | — | 0.40 [0.36, 0.45]; n=1000 | —; n=1 |
| Sonnet | — | 0.35 [0.31, 0.39]; n=1000 | 0.40 [0.36, 0.45]; n=1000 | — | —; n=1 |
| GLM | — | —; n=1 | —; n=1 | —; n=1 | — |

## Tau Ceti

Full-pass cost reference: **1000 targets**, the largest completed pass in this group.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 1000 | 1/1 | 1000/1000 | 50 | 50 | 5.0% [3.8%, 6.5%] | $49.56 / $49.56 |
| Sol | 1000 | 1/1 | 1000/1000 | 142 | 142 | 14.2% [12.2%, 16.5%] | $64.21 / $64.21 |
| Luna | 1000 | 1/1 | 1000/1000 | 150 | 150 | 15.0% [12.9%, 17.3%] | $3.27 / $3.27 |
| Sonnet | 1000 | 1/1 | 1000/1000 | 35 | 35 | 3.5% [2.5%, 4.8%] | $20.80 / $20.80 |
| GLM | 10 | 0/1 | 1/10 | 0 | 0 | 0.0% [0.0%, 79.3%] | $0.00 / $2.11 |

### Correlation matrix

Cells: r [95% CI]; n is the number of matched targets.

| Model | Opus | Sol | Luna | Sonnet | GLM |
|---|---:|---:|---:|---:|---:|
| Opus | — | 0.55 [0.48, 0.62]; n=1000 | 0.51 [0.44, 0.58]; n=1000 | 0.66 [0.53, 0.76]; n=1000 | —; n=1 |
| Sol | 0.55 [0.48, 0.62]; n=1000 | — | 0.64 [0.57, 0.71]; n=1000 | 0.45 [0.37, 0.53]; n=1000 | —; n=1 |
| Luna | 0.51 [0.44, 0.58]; n=1000 | 0.64 [0.57, 0.71]; n=1000 | — | 0.41 [0.33, 0.48]; n=1000 | —; n=1 |
| Sonnet | 0.66 [0.53, 0.76]; n=1000 | 0.45 [0.37, 0.53]; n=1000 | 0.41 [0.33, 0.48]; n=1000 | — | —; n=1 |
| GLM | —; n=1 | —; n=1 | —; n=1 | —; n=1 | — |

## Lean Pool

Full-pass cost reference: **1000 targets**, the largest completed pass in this group.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 1000 | 1/1 | 1000/1000 | 68 | 68 | 6.8% [5.4%, 8.5%] | $40.48 / $40.48 |
| Sol | 1000 | 1/1 | 1000/1000 | 149 | 149 | 14.9% [12.8%, 17.2%] | $60.29 / $60.29 |
| Luna | 1000 | 1/1 | 1000/1000 | 147 | 147 | 14.7% [12.6%, 17.0%] | $2.88 / $2.88 |
| Sonnet | 1000 | 1/1 | 1000/1000 | 58 | 58 | 5.8% [4.5%, 7.4%] | $17.79 / $17.79 |
| GLM | 10 | 0/1 | 1/10 | 0 | 0 | 0.0% [0.0%, 79.3%] | $0.01 / $14.03 |

### Correlation matrix

Cells: r [95% CI]; n is the number of matched targets.

| Model | Opus | Sol | Luna | Sonnet | GLM |
|---|---:|---:|---:|---:|---:|
| Opus | — | 0.62 [0.55, 0.69]; n=1000 | 0.62 [0.55, 0.68]; n=1000 | 0.82 [0.74, 0.88]; n=1000 | —; n=1 |
| Sol | 0.62 [0.55, 0.69]; n=1000 | — | 0.74 [0.68, 0.80]; n=1000 | 0.57 [0.50, 0.63]; n=1000 | —; n=1 |
| Luna | 0.62 [0.55, 0.68]; n=1000 | 0.74 [0.68, 0.80]; n=1000 | — | 0.53 [0.45, 0.60]; n=1000 | —; n=1 |
| Sonnet | 0.82 [0.74, 0.88]; n=1000 | 0.57 [0.50, 0.63]; n=1000 | 0.53 [0.45, 0.60]; n=1000 | — | —; n=1 |
| GLM | —; n=1 | —; n=1 | —; n=1 | —; n=1 | — |

## FLT (Anthropic)

Full-pass cost reference: **1000 targets**, the largest completed pass in this group.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 1000 | 1/1 | 1000/1000 | 137 | 137 | 13.7% [11.7%, 16.0%] | $70.21 / $70.21 |
| Sol | 1000 | 1/1 | 1000/1000 | 255 | 255 | 25.5% [22.9%, 28.3%] | $73.09 / $73.09 |
| Luna | 1000 | 1/1 | 1000/1000 | 230 | 230 | 23.0% [20.5%, 25.7%] | $3.58 / $3.58 |
| Sonnet | 1000 | 1/1 | 1000/1000 | 118 | 118 | 11.8% [9.9%, 13.9%] | $30.27 / $30.27 |
| GLM | 10 | 0/1 | 1/10 | 1 | 1 | 100.0% [20.7%, 100.0%] | $0.06 / $62.87 |

### Correlation matrix

Cells: r [95% CI]; n is the number of matched targets.

| Model | Opus | Sol | Luna | Sonnet | GLM |
|---|---:|---:|---:|---:|---:|
| Opus | — | 0.65 [0.60, 0.70]; n=1000 | 0.64 [0.58, 0.69]; n=1000 | 0.75 [0.68, 0.80]; n=1000 | —; n=1 |
| Sol | 0.65 [0.60, 0.70]; n=1000 | — | 0.70 [0.65, 0.75]; n=1000 | 0.53 [0.47, 0.59]; n=1000 | —; n=1 |
| Luna | 0.64 [0.58, 0.69]; n=1000 | 0.70 [0.65, 0.75]; n=1000 | — | 0.58 [0.52, 0.64]; n=1000 | —; n=1 |
| Sonnet | 0.75 [0.68, 0.80]; n=1000 | 0.53 [0.47, 0.59]; n=1000 | 0.58 [0.52, 0.64]; n=1000 | — | —; n=1 |
| GLM | —; n=1 | —; n=1 | —; n=1 | —; n=1 | — |

## Formal Frontier

Full-pass cost reference: **1000 targets**, the largest completed pass in this group.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 1000 | 1/1 | 1000/1000 | 46 | 46 | 4.6% [3.5%, 6.1%] | $56.04 / $56.04 |
| Sol | 1000 | 1/1 | 1000/1000 | 212 | 212 | 21.2% [18.8%, 23.8%] | $67.53 / $67.53 |
| Luna | 1000 | 1/1 | 1000/1000 | 229 | 229 | 22.9% [20.4%, 25.6%] | $3.55 / $3.55 |
| Sonnet | 1000 | 1/1 | 1000/1000 | 45 | 45 | 4.5% [3.4%, 6.0%] | $25.75 / $25.75 |
| GLM | 10 | 0/1 | 0/10 | 0 | 0 | — | $0.00 / — |

### Correlation matrix

Cells: r [95% CI]; n is the number of matched targets.

| Model | Opus | Sol | Luna | Sonnet | GLM |
|---|---:|---:|---:|---:|---:|
| Opus | — | 0.41 [0.35, 0.47]; n=1000 | 0.39 [0.33, 0.45]; n=1000 | 0.67 [0.54, 0.77]; n=1000 | — |
| Sol | 0.41 [0.35, 0.47]; n=1000 | — | 0.58 [0.52, 0.64]; n=1000 | 0.30 [0.22, 0.37]; n=1000 | — |
| Luna | 0.39 [0.33, 0.45]; n=1000 | 0.58 [0.52, 0.64]; n=1000 | — | 0.40 [0.34, 0.45]; n=1000 | — |
| Sonnet | 0.67 [0.54, 0.77]; n=1000 | 0.30 [0.22, 0.37]; n=1000 | 0.40 [0.34, 0.45]; n=1000 | — | — |
| GLM | — | — | — | — | — |
