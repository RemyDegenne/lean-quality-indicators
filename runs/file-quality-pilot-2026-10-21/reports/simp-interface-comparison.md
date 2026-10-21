# simp-interface

Generated 2026-10-21T06:58:55+00:00 · [Methods and notation](../../../AUDIT_METHODS.md) · 2,000 bootstrap draws.

## Library comparison

| Library | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Mathlib | — | — | 4/10<br>40.0% [16.8%, 68.7%] | 4/10<br>40.0% [16.8%, 68.7%] |
| Tau Ceti | — | — | 3/10<br>30.0% [10.8%, 60.3%] | 1/10<br>10.0% [1.8%, 40.4%] |
| Lean Pool | — | — | 6/10<br>60.0% [31.3%, 83.2%] | 6/10<br>60.0% [31.3%, 83.2%] |
| OpenAI Math | 8/14<br>57.1% [32.6%, 78.6%] | 2/9<br>22.2% [6.3%, 54.7%] | 12/22<br>54.5% [34.7%, 73.1%] | 7/20<br>35.0% [18.1%, 56.7%] |

## All libraries

Full-pass reference: **30 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 100 | 0/1 | 14/100 | 8 | 8 | 57.1% [32.6%, 78.6%] | $3.74 / $8.01 |
| Sol | 100 | 0/1 | 9/100 | 2 | 2 | 22.2% [6.3%, 54.7%] | $0.96 / $3.21 |
| Sonnet | 130 | 0/1 | 52/130 | 25 | 25 | 48.1% [35.1%, 61.3%] | $4.51 / $2.60 |
| Luna | 130 | 0/1 | 50/130 | 18 | 18 | 36.0% [24.1%, 49.9%] | $0.24 / $0.14 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Opus | — | 0.38 [—]; n=9 | 0.71 [0.26, 1.00]; n=14 | 0.65 [0.35, 1.00]; n=14 |
| Sol | 0.38 [—]; n=9 | — | 0.38 [—]; n=9 | 0.19 [—]; n=9 |
| Sonnet | 0.71 [0.26, 1.00]; n=14 | 0.38 [—]; n=9 | — | 0.39 [0.14, 0.63]; n=50 |
| Luna | 0.65 [0.35, 1.00]; n=14 | 0.19 [—]; n=9 | 0.39 [0.14, 0.63]; n=50 | — |

Coverage annotations: Opus: 0 partial, 1 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 3 not applicable; Luna: 0 partial, 0 not applicable.

## Mathlib

Full-pass reference: **10 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sol | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sonnet | 10 | 1/1 | 10/10 | 4 | 4 | 40.0% [16.8%, 68.7%] | $0.68 / $0.68 |
| Luna | 10 | 1/1 | 10/10 | 4 | 4 | 40.0% [16.8%, 68.7%] | $0.05 / $0.05 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Opus | — | — | — | — |
| Sol | — | — | — | — |
| Sonnet | — | — | — | 0.58 [0.00, 1.00]; n=10 |
| Luna | — | — | 0.58 [0.00, 1.00]; n=10 | — |

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 1 not applicable; Luna: 0 partial, 0 not applicable.

## Tau Ceti

Full-pass reference: **10 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sol | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sonnet | 10 | 1/1 | 10/10 | 3 | 3 | 30.0% [10.8%, 60.3%] | $0.68 / $0.68 |
| Luna | 10 | 1/1 | 10/10 | 1 | 1 | 10.0% [1.8%, 40.4%] | $0.05 / $0.05 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Opus | — | — | — | — |
| Sol | — | — | — | — |
| Sonnet | — | — | — | -0.22 [—]; n=10 |
| Luna | — | — | -0.22 [—]; n=10 | — |

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 0 not applicable; Luna: 0 partial, 0 not applicable.

## Lean Pool

Full-pass reference: **10 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sol | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sonnet | 10 | 1/1 | 10/10 | 6 | 6 | 60.0% [31.3%, 83.2%] | $1.04 / $1.04 |
| Luna | 10 | 1/1 | 10/10 | 6 | 6 | 60.0% [31.3%, 83.2%] | $0.06 / $0.06 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Opus | — | — | — | — |
| Sol | — | — | — | — |
| Sonnet | — | — | — | 0.58 [-0.17, 1.00]; n=10 |
| Luna | — | — | 0.58 [-0.17, 1.00]; n=10 | — |

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 0 not applicable; Luna: 0 partial, 0 not applicable.

## OpenAI Math

Full-pass reference: **0 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 100 | 0/1 | 14/100 | 8 | 8 | 57.1% [32.6%, 78.6%] | $3.74 / $0.00 |
| Sol | 100 | 0/1 | 9/100 | 2 | 2 | 22.2% [6.3%, 54.7%] | $0.96 / $0.00 |
| Sonnet | 100 | 0/1 | 22/100 | 12 | 12 | 54.5% [34.7%, 73.1%] | $2.12 / $0.00 |
| Luna | 100 | 0/1 | 20/100 | 7 | 7 | 35.0% [18.1%, 56.7%] | $0.09 / $0.00 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Opus | — | 0.38 [—]; n=9 | 0.71 [0.29, 1.00]; n=14 | 0.65 [0.35, 1.00]; n=14 |
| Sol | 0.38 [—]; n=9 | — | 0.38 [—]; n=9 | 0.19 [—]; n=9 |
| Sonnet | 0.71 [0.29, 1.00]; n=14 | 0.38 [—]; n=9 | — | 0.31 [-0.10, 0.70]; n=20 |
| Luna | 0.65 [0.35, 1.00]; n=14 | 0.19 [—]; n=9 | 0.31 [-0.10, 0.70]; n=20 | — |

Coverage annotations: Opus: 0 partial, 1 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 2 not applicable; Luna: 0 partial, 0 not applicable.
