# readable-proof-simplification

Generated 2026-10-21T06:58:56+00:00 · [Methods and notation](../../../AUDIT_METHODS.md) · 2,000 bootstrap draws.

## Library comparison

| Library | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Mathlib | — | — | 7/10<br>70.0% [39.7%, 89.2%] | 2/10<br>20.0% [5.7%, 51.0%] |
| Tau Ceti | — | — | 8/10<br>80.0% [49.0%, 94.3%] | 3/10<br>30.0% [10.8%, 60.3%] |
| Lean Pool | — | — | 9/10<br>90.0% [59.6%, 98.2%] | 6/10<br>60.0% [31.3%, 83.2%] |
| OpenAI Math | 11/14<br>78.6% [52.4%, 92.4%] | 6/9<br>66.7% [35.4%, 87.9%] | 16/21<br>76.2% [54.9%, 89.4%] | 4/19<br>21.1% [8.5%, 43.3%] |

## All libraries

Full-pass reference: **30 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 100 | 0/1 | 14/100 | 11 | 11 | 78.6% [52.4%, 92.4%] | $4.36 / $9.34 |
| Sol | 100 | 0/1 | 9/100 | 6 | 6 | 66.7% [35.4%, 87.9%] | $1.16 / $3.85 |
| Sonnet | 130 | 0/1 | 51/130 | 40 | 40 | 78.4% [65.4%, 87.5%] | $6.20 / $3.65 |
| Luna | 130 | 0/1 | 49/130 | 15 | 15 | 30.6% [19.5%, 44.5%] | $0.20 / $0.12 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Opus | — | 0.19 [—]; n=9 | 0.83 [—]; n=14 | 0.27 [—]; n=14 |
| Sol | 0.19 [—]; n=9 | — | 0.50 [—]; n=9 | 0.38 [—]; n=9 |
| Sonnet | 0.83 [—]; n=14 | 0.50 [—]; n=9 | — | 0.36 [0.22, 0.48]; n=49 |
| Luna | 0.27 [—]; n=14 | 0.38 [—]; n=9 | 0.36 [0.22, 0.48]; n=49 | — |

Coverage annotations: Opus: 0 partial, 1 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 1 not applicable; Luna: 0 partial, 1 not applicable.

## Mathlib

Full-pass reference: **10 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sol | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sonnet | 10 | 1/1 | 10/10 | 7 | 7 | 70.0% [39.7%, 89.2%] | $0.91 / $0.91 |
| Luna | 10 | 1/1 | 10/10 | 2 | 2 | 20.0% [5.7%, 51.0%] | $0.03 / $0.03 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Opus | — | — | — | — |
| Sol | — | — | — | — |
| Sonnet | — | — | — | 0.33 [—]; n=10 |
| Luna | — | — | 0.33 [—]; n=10 | — |

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 0 not applicable; Luna: 0 partial, 0 not applicable.

## Tau Ceti

Full-pass reference: **10 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sol | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sonnet | 10 | 1/1 | 10/10 | 8 | 8 | 80.0% [49.0%, 94.3%] | $1.06 / $1.06 |
| Luna | 10 | 1/1 | 10/10 | 3 | 3 | 30.0% [10.8%, 60.3%] | $0.03 / $0.03 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Opus | — | — | — | — |
| Sol | — | — | — | — |
| Sonnet | — | — | — | 0.33 [—]; n=10 |
| Luna | — | — | 0.33 [—]; n=10 | — |

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 0 not applicable; Luna: 0 partial, 0 not applicable.

## Lean Pool

Full-pass reference: **10 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sol | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sonnet | 10 | 1/1 | 10/10 | 9 | 9 | 90.0% [59.6%, 98.2%] | $1.54 / $1.54 |
| Luna | 10 | 1/1 | 10/10 | 6 | 6 | 60.0% [31.3%, 83.2%] | $0.05 / $0.05 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Opus | — | — | — | — |
| Sol | — | — | — | — |
| Sonnet | — | — | — | 0.41 [—]; n=10 |
| Luna | — | — | 0.41 [—]; n=10 | — |

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 0 not applicable; Luna: 0 partial, 0 not applicable.

## OpenAI Math

Full-pass reference: **0 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 100 | 0/1 | 14/100 | 11 | 11 | 78.6% [52.4%, 92.4%] | $4.36 / $0.00 |
| Sol | 100 | 0/1 | 9/100 | 6 | 6 | 66.7% [35.4%, 87.9%] | $1.16 / $0.00 |
| Sonnet | 100 | 0/1 | 21/100 | 16 | 16 | 76.2% [54.9%, 89.4%] | $2.69 / $0.00 |
| Luna | 100 | 0/1 | 19/100 | 4 | 4 | 21.1% [8.5%, 43.3%] | $0.08 / $0.00 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Opus | — | 0.19 [—]; n=9 | 0.83 [—]; n=14 | 0.27 [—]; n=14 |
| Sol | 0.19 [—]; n=9 | — | 0.50 [—]; n=9 | 0.38 [—]; n=9 |
| Sonnet | 0.83 [—]; n=14 | 0.50 [—]; n=9 | — | 0.31 [0.12, 0.52]; n=19 |
| Luna | 0.27 [—]; n=14 | 0.38 [—]; n=9 | 0.31 [0.12, 0.52]; n=19 | — |

Coverage annotations: Opus: 0 partial, 1 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 1 not applicable; Luna: 0 partial, 1 not applicable.
