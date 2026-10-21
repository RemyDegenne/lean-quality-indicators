# readable-proof-simplification

Generated 2026-10-21T07:24:42+00:00 · [Methods and notation](../../../AUDIT_METHODS.md) · 2,000 bootstrap draws.

## Library comparison

| Library | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Mathlib | — | — | 7/10<br>70.0% [39.7%, 89.2%] | 2/10<br>20.0% [5.7%, 51.0%] | — |
| Tau Ceti | — | — | 8/10<br>80.0% [49.0%, 94.3%] | 3/10<br>30.0% [10.8%, 60.3%] | — |
| Lean Pool | — | — | 9/10<br>90.0% [59.6%, 98.2%] | 6/10<br>60.0% [31.3%, 83.2%] | — |
| OpenAI Math | 15/19<br>78.9% [56.7%, 91.5%] | 8/14<br>57.1% [32.6%, 78.6%] | 22/28<br>78.6% [60.5%, 89.8%] | 5/25<br>20.0% [8.9%, 39.1%] | — |

## All libraries

Full-pass reference: **30 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 100 | 0/1 | 19/100 | 15 | 15 | 78.9% [56.7%, 91.5%] | $6.06 / $9.56 |
| Sol | 100 | 0/1 | 14/100 | 8 | 8 | 57.1% [32.6%, 78.6%] | $1.68 / $3.61 |
| Sonnet | 130 | 0/1 | 58/130 | 46 | 46 | 79.3% [67.2%, 87.7%] | $7.41 / $3.83 |
| Luna | 130 | 0/1 | 55/130 | 16 | 16 | 29.1% [18.8%, 42.1%] | $0.21 / $0.12 |
| DeepSeek | 40 | 0/1 | 0/40 | 0 | 0 | — | $0.00 / — |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | 0.41 [-0.17, 0.85]; n=14 | 0.57 [-0.02, 1.00]; n=19 | 0.27 [—]; n=19 | — |
| Sol | 0.41 [-0.17, 0.85]; n=14 | — | 0.41 [-0.18, 0.86]; n=14 | 0.10 [-0.45, 0.55]; n=14 | — |
| Sonnet | 0.57 [-0.02, 1.00]; n=19 | 0.41 [-0.18, 0.86]; n=14 | — | 0.34 [0.23, 0.46]; n=55 | — |
| Luna | 0.27 [—]; n=19 | 0.10 [-0.45, 0.55]; n=14 | 0.34 [0.23, 0.46]; n=55 | — | — |
| DeepSeek | — | — | — | — | — |

Coverage annotations: Opus: 0 partial, 1 not applicable; Sol: 0 partial, 1 not applicable; Sonnet: 0 partial, 1 not applicable; Luna: 0 partial, 1 not applicable; DeepSeek: 0 partial, 0 not applicable.

## Mathlib

Full-pass reference: **10 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sol | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sonnet | 10 | 1/1 | 10/10 | 7 | 7 | 70.0% [39.7%, 89.2%] | $0.91 / $0.91 |
| Luna | 10 | 1/1 | 10/10 | 2 | 2 | 20.0% [5.7%, 51.0%] | $0.03 / $0.03 |
| DeepSeek | 10 | 0/1 | 0/10 | 0 | 0 | — | $0.00 / — |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | — | — | — | — |
| Sol | — | — | — | — | — |
| Sonnet | — | — | — | 0.33 [—]; n=10 | — |
| Luna | — | — | 0.33 [—]; n=10 | — | — |
| DeepSeek | — | — | — | — | — |

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 0 not applicable; Luna: 0 partial, 0 not applicable; DeepSeek: 0 partial, 0 not applicable.

## Tau Ceti

Full-pass reference: **10 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sol | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sonnet | 10 | 1/1 | 10/10 | 8 | 8 | 80.0% [49.0%, 94.3%] | $1.06 / $1.06 |
| Luna | 10 | 1/1 | 10/10 | 3 | 3 | 30.0% [10.8%, 60.3%] | $0.03 / $0.03 |
| DeepSeek | 10 | 0/1 | 0/10 | 0 | 0 | — | $0.00 / — |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | — | — | — | — |
| Sol | — | — | — | — | — |
| Sonnet | — | — | — | 0.33 [—]; n=10 | — |
| Luna | — | — | 0.33 [—]; n=10 | — | — |
| DeepSeek | — | — | — | — | — |

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 0 not applicable; Luna: 0 partial, 0 not applicable; DeepSeek: 0 partial, 0 not applicable.

## Lean Pool

Full-pass reference: **10 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sol | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sonnet | 10 | 1/1 | 10/10 | 9 | 9 | 90.0% [59.6%, 98.2%] | $1.54 / $1.54 |
| Luna | 10 | 1/1 | 10/10 | 6 | 6 | 60.0% [31.3%, 83.2%] | $0.05 / $0.05 |
| DeepSeek | 10 | 0/1 | 0/10 | 0 | 0 | — | $0.00 / — |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | — | — | — | — |
| Sol | — | — | — | — | — |
| Sonnet | — | — | — | 0.41 [—]; n=10 | — |
| Luna | — | — | 0.41 [—]; n=10 | — | — |
| DeepSeek | — | — | — | — | — |

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 0 not applicable; Luna: 0 partial, 0 not applicable; DeepSeek: 0 partial, 0 not applicable.

## OpenAI Math

Full-pass reference: **0 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 100 | 0/1 | 19/100 | 15 | 15 | 78.9% [56.7%, 91.5%] | $6.06 / $0.00 |
| Sol | 100 | 0/1 | 14/100 | 8 | 8 | 57.1% [32.6%, 78.6%] | $1.68 / $0.00 |
| Sonnet | 100 | 0/1 | 28/100 | 22 | 22 | 78.6% [60.5%, 89.8%] | $3.90 / $0.00 |
| Luna | 100 | 0/1 | 25/100 | 5 | 5 | 20.0% [8.9%, 39.1%] | $0.09 / $0.00 |
| DeepSeek | 10 | 0/1 | 0/10 | 0 | 0 | — | $0.00 / — |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | 0.41 [-0.17, 0.85]; n=14 | 0.57 [0.05, 1.00]; n=19 | 0.27 [0.10, 0.46]; n=19 | — |
| Sol | 0.41 [-0.17, 0.85]; n=14 | — | 0.41 [-0.18, 0.86]; n=14 | 0.10 [—]; n=14 | — |
| Sonnet | 0.57 [0.05, 1.00]; n=19 | 0.41 [-0.18, 0.86]; n=14 | — | 0.28 [0.13, 0.46]; n=25 | — |
| Luna | 0.27 [0.10, 0.46]; n=19 | 0.10 [—]; n=14 | 0.28 [0.13, 0.46]; n=25 | — | — |
| DeepSeek | — | — | — | — | — |

Coverage annotations: Opus: 0 partial, 1 not applicable; Sol: 0 partial, 1 not applicable; Sonnet: 0 partial, 1 not applicable; Luna: 0 partial, 1 not applicable; DeepSeek: 0 partial, 0 not applicable.
