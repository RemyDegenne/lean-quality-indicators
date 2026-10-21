# unnecessary-hypotheses

Generated 2026-10-21T05:09:10+00:00.

Targets are distinct selected source files/theorems, not findings. A judgment is flagged when it reports at least one finding. Passes show completed / planned; an unfinished pass is included in the judgment and flag counts. The flag-rate interval uses the first pass only, with Wilson 95% limits; repeated judgments are not treated as independent targets.

Correlations are Pearson r on binary flag decisions (the phi coefficient). Cross-model cells use matching completed targets from each model's first pass. Diagonal cells compare the first two independent passes, where available. Intervals are paired-target percentile bootstrap 95% intervals, stratified by library (2,000 draws, fixed seeds). A dash means no estimate/interval: insufficient matches, constant decisions, a boundary estimate or too many degenerate resamples. The intervals describe sampling uncertainty, not correctness against ground truth. First-pass and repeat-pass matches need not have the same n.

Expenditure cells are **$X / $Y** in USD at API-equivalent rates. X is recorded expenditure to date, including retained retry usage. Y estimates a single pass at the largest completed pass's target count, using this model's expenditure per completed judgment across its passes. Y is an extrapolation when coverage is smaller; it does not assume equal token use or prices across models. Deleted or overwritten usage cannot be reconstructed. See the [cost methods and rates](../api-equivalent-costs.md).

Opus selected 400 targets/library for its first pass and 300/library for its second; the other completed models selected 300/library for each pass. Selected targets are counted once across passes.

## All libraries

Full-pass cost reference: **2000 targets**, the largest completed pass in this group.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 2000 | 2/2 | 3500/3500 | 348 | 205 | 9.9% [8.7%, 11.3%] | $254.27 / $145.30 |
| Sol | 1500 | 2/2 | 3000/3000 | 374 | 189 | 12.5% [10.9%, 14.2%] | $140.71 / $93.81 |
| Luna | 1500 | 2/2 | 3000/3000 | 310 | 193 | 10.3% [8.9%, 12.0%] | $6.51 / $4.34 |
| Sonnet | 1500 | 2/2 | 3000/3000 | 245 | 137 | 8.1% [6.8%, 9.6%] | $105.40 / $70.27 |
| GLM | 50 | 0/1 | 4/50 | 1 | 1 | 25.0% [4.6%, 69.9%] | $0.49 / $245.16 |

### Correlation matrix

Cells: r [95% CI]; n is the number of matched targets.

| Model | Opus | Sol | Luna | Sonnet | GLM |
|---|---:|---:|---:|---:|---:|
| Opus | 0.92 [0.89, 0.95]; n=1500 | 0.91 [0.87, 0.94]; n=1500 | 0.73 [0.67, 0.78]; n=1500 | 0.85 [0.80, 0.89]; n=1500 | 1.00 [—]; n=4 |
| Sol | 0.91 [0.87, 0.94]; n=1500 | 0.99 [0.97, 1.00]; n=1500 | 0.70 [0.64, 0.76]; n=1500 | 0.78 [0.73, 0.82]; n=1500 | 1.00 [—]; n=4 |
| Luna | 0.73 [0.67, 0.78]; n=1500 | 0.70 [0.64, 0.76]; n=1500 | 0.73 [0.67, 0.78]; n=1500 | 0.70 [0.64, 0.76]; n=1500 | 1.00 [—]; n=4 |
| Sonnet | 0.85 [0.80, 0.89]; n=1500 | 0.78 [0.73, 0.82]; n=1500 | 0.70 [0.64, 0.76]; n=1500 | 0.87 [0.82, 0.91]; n=1500 | 1.00 [—]; n=4 |
| GLM | 1.00 [—]; n=4 | 1.00 [—]; n=4 | 1.00 [—]; n=4 | 1.00 [—]; n=4 | — |

## Mathlib

Full-pass cost reference: **400 targets**, the largest completed pass in this group.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 400 | 2/2 | 700/700 | 24 | 15 | 3.8% [2.3%, 6.1%] | $26.82 / $15.33 |
| Sol | 300 | 2/2 | 600/600 | 24 | 12 | 4.0% [2.3%, 6.9%] | $21.13 / $14.09 |
| Luna | 300 | 2/2 | 600/600 | 23 | 16 | 4.0% [2.3%, 6.9%] | $1.00 / $0.67 |
| Sonnet | 300 | 2/2 | 600/600 | 13 | 8 | 2.0% [0.9%, 4.3%] | $10.55 / $7.04 |
| GLM | 10 | 0/1 | 1/10 | 0 | 0 | 0.0% [0.0%, 79.3%] | $0.01 / $3.19 |

### Correlation matrix

Cells: r [95% CI]; n is the number of matched targets.

| Model | Opus | Sol | Luna | Sonnet | GLM |
|---|---:|---:|---:|---:|---:|
| Opus | 0.90 [0.73, 1.00]; n=300 | 0.96 [0.86, 1.00]; n=300 | 0.68 [0.41, 0.88]; n=300 | 0.73 [0.49, 0.92]; n=300 | —; n=1 |
| Sol | 0.96 [0.86, 1.00]; n=300 | 1.00 [—]; n=300 | 0.65 [0.39, 0.85]; n=300 | 0.70 [0.44, 0.89]; n=300 | —; n=1 |
| Luna | 0.68 [0.41, 0.88]; n=300 | 0.65 [0.39, 0.85]; n=300 | 0.59 [0.30, 0.81]; n=300 | 0.46 [0.12, 0.73]; n=300 | —; n=1 |
| Sonnet | 0.73 [0.49, 0.92]; n=300 | 0.70 [0.44, 0.89]; n=300 | 0.46 [0.12, 0.73]; n=300 | 0.77 [0.40, 1.00]; n=300 | —; n=1 |
| GLM | —; n=1 | —; n=1 | —; n=1 | —; n=1 | — |

## Tau Ceti

Full-pass cost reference: **400 targets**, the largest completed pass in this group.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 400 | 2/2 | 700/700 | 37 | 23 | 5.8% [3.9%, 8.5%] | $55.63 / $31.79 |
| Sol | 300 | 2/2 | 600/600 | 37 | 19 | 6.3% [4.1%, 9.7%] | $28.13 / $18.76 |
| Luna | 300 | 2/2 | 600/600 | 37 | 25 | 6.3% [4.1%, 9.7%] | $1.39 / $0.92 |
| Sonnet | 300 | 2/2 | 600/600 | 22 | 12 | 4.0% [2.3%, 6.9%] | $22.55 / $15.03 |
| GLM | 10 | 0/1 | 1/10 | 0 | 0 | 0.0% [0.0%, 79.3%] | $0.43 / $173.23 |

### Correlation matrix

Cells: r [95% CI]; n is the number of matched targets.

| Model | Opus | Sol | Luna | Sonnet | GLM |
|---|---:|---:|---:|---:|---:|
| Opus | 0.96 [0.88, 1.00]; n=300 | 0.88 [0.76, 0.97]; n=300 | 0.51 [0.28, 0.70]; n=300 | 0.89 [0.75, 1.00]; n=300 | —; n=1 |
| Sol | 0.88 [0.76, 0.97]; n=300 | 0.97 [0.90, 1.00]; n=300 | 0.44 [0.21, 0.63]; n=300 | 0.79 [0.62, 0.92]; n=300 | —; n=1 |
| Luna | 0.51 [0.28, 0.70]; n=300 | 0.44 [0.21, 0.63]; n=300 | 0.63 [0.40, 0.80]; n=300 | 0.58 [0.36, 0.77]; n=300 | —; n=1 |
| Sonnet | 0.89 [0.75, 1.00]; n=300 | 0.79 [0.62, 0.92]; n=300 | 0.58 [0.36, 0.77]; n=300 | 0.91 [0.77, 1.00]; n=300 | —; n=1 |
| GLM | —; n=1 | —; n=1 | —; n=1 | —; n=1 | — |

## Lean Pool

Full-pass cost reference: **400 targets**, the largest completed pass in this group.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 400 | 2/2 | 700/700 | 109 | 62 | 15.2% [12.1%, 19.1%] | $54.71 / $31.26 |
| Sol | 300 | 2/2 | 600/600 | 121 | 61 | 20.0% [15.9%, 24.9%] | $28.55 / $19.03 |
| Luna | 300 | 2/2 | 600/600 | 99 | 56 | 16.0% [12.3%, 20.6%] | $1.37 / $0.91 |
| Sonnet | 300 | 2/2 | 600/600 | 81 | 46 | 13.0% [9.7%, 17.3%] | $20.92 / $13.95 |
| GLM | 10 | 0/1 | 1/10 | 1 | 1 | 100.0% [20.7%, 100.0%] | $0.01 / $4.40 |

### Correlation matrix

Cells: r [95% CI]; n is the number of matched targets.

| Model | Opus | Sol | Luna | Sonnet | GLM |
|---|---:|---:|---:|---:|---:|
| Opus | 0.93 [0.87, 0.98]; n=300 | 0.92 [0.86, 0.97]; n=300 | 0.86 [0.77, 0.93]; n=300 | 0.84 [0.76, 0.92]; n=300 | —; n=1 |
| Sol | 0.92 [0.86, 0.97]; n=300 | 0.99 [0.97, 1.00]; n=300 | 0.83 [0.75, 0.90]; n=300 | 0.77 [0.68, 0.85]; n=300 | —; n=1 |
| Luna | 0.86 [0.77, 0.93]; n=300 | 0.83 [0.75, 0.90]; n=300 | 0.84 [0.76, 0.92]; n=300 | 0.80 [0.70, 0.89]; n=300 | —; n=1 |
| Sonnet | 0.84 [0.76, 0.92]; n=300 | 0.77 [0.68, 0.85]; n=300 | 0.80 [0.70, 0.89]; n=300 | 0.84 [0.75, 0.92]; n=300 | —; n=1 |
| GLM | —; n=1 | —; n=1 | —; n=1 | —; n=1 | — |

## FLT (Anthropic)

Full-pass cost reference: **400 targets**, the largest completed pass in this group.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 400 | 2/2 | 700/700 | 146 | 87 | 20.5% [16.8%, 24.7%] | $72.31 / $41.32 |
| Sol | 300 | 2/2 | 600/600 | 157 | 79 | 26.0% [21.4%, 31.2%] | $37.40 / $24.93 |
| Luna | 300 | 2/2 | 600/600 | 121 | 77 | 20.3% [16.2%, 25.2%] | $1.61 / $1.07 |
| Sonnet | 300 | 2/2 | 600/600 | 106 | 59 | 17.3% [13.5%, 22.0%] | $30.12 / $20.08 |
| GLM | 10 | 0/1 | 1/10 | 0 | 0 | 0.0% [0.0%, 79.3%] | $0.04 / $15.31 |

### Correlation matrix

Cells: r [95% CI]; n is the number of matched targets.

| Model | Opus | Sol | Luna | Sonnet | GLM |
|---|---:|---:|---:|---:|---:|
| Opus | 0.90 [0.83, 0.96]; n=300 | 0.88 [0.82, 0.93]; n=300 | 0.69 [0.58, 0.78]; n=300 | 0.84 [0.75, 0.91]; n=300 | —; n=1 |
| Sol | 0.88 [0.82, 0.93]; n=300 | 0.99 [0.97, 1.00]; n=300 | 0.68 [0.58, 0.77]; n=300 | 0.75 [0.67, 0.82]; n=300 | —; n=1 |
| Luna | 0.69 [0.58, 0.78]; n=300 | 0.68 [0.58, 0.77]; n=300 | 0.66 [0.54, 0.76]; n=300 | 0.67 [0.55, 0.77]; n=300 | —; n=1 |
| Sonnet | 0.84 [0.75, 0.91]; n=300 | 0.75 [0.67, 0.82]; n=300 | 0.67 [0.55, 0.77]; n=300 | 0.86 [0.78, 0.93]; n=300 | —; n=1 |
| GLM | —; n=1 | —; n=1 | —; n=1 | —; n=1 | — |

## Formal Frontier

Full-pass cost reference: **400 targets**, the largest completed pass in this group.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 400 | 2/2 | 700/700 | 32 | 18 | 4.2% [2.7%, 6.7%] | $44.81 / $25.60 |
| Sol | 300 | 2/2 | 600/600 | 35 | 18 | 6.0% [3.8%, 9.3%] | $25.49 / $16.99 |
| Luna | 300 | 2/2 | 600/600 | 30 | 19 | 5.0% [3.1%, 8.1%] | $1.14 / $0.76 |
| Sonnet | 300 | 2/2 | 600/600 | 23 | 12 | 4.0% [2.3%, 6.9%] | $21.25 / $14.17 |
| GLM | 10 | 0/1 | 0/10 | 0 | 0 | — | $0.00 / — |

### Correlation matrix

Cells: r [95% CI]; n is the number of matched targets.

| Model | Opus | Sol | Luna | Sonnet | GLM |
|---|---:|---:|---:|---:|---:|
| Opus | 0.93 [0.81, 1.00]; n=300 | 0.91 [0.79, 1.00]; n=300 | 0.65 [0.42, 0.83]; n=300 | 0.89 [0.75, 1.00]; n=300 | — |
| Sol | 0.91 [0.79, 1.00]; n=300 | 0.97 [0.89, 1.00]; n=300 | 0.59 [0.35, 0.77]; n=300 | 0.81 [0.64, 0.94]; n=300 | — |
| Luna | 0.65 [0.42, 0.83]; n=300 | 0.59 [0.35, 0.77]; n=300 | 0.72 [0.50, 0.89]; n=300 | 0.73 [0.51, 0.90]; n=300 | — |
| Sonnet | 0.89 [0.75, 1.00]; n=300 | 0.81 [0.64, 0.94]; n=300 | 0.73 [0.51, 0.90]; n=300 | 0.96 [0.84, 1.00]; n=300 | — |
| GLM | — | — | — | — | — |
