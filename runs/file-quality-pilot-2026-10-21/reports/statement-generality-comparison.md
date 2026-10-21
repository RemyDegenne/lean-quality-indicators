# statement-generality

Generated 2026-10-21T06:58:55+00:00 · [Methods and notation](../../../AUDIT_METHODS.md) · 2,000 bootstrap draws.

## Library comparison

| Library | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Mathlib | — | — | 6/10<br>60.0% [31.3%, 83.2%] | 2/10<br>20.0% [5.7%, 51.0%] |
| Tau Ceti | — | — | 3/10<br>30.0% [10.8%, 60.3%] | 1/10<br>10.0% [1.8%, 40.4%] |
| Lean Pool | — | — | 9/10<br>90.0% [59.6%, 98.2%] | 8/10<br>80.0% [49.0%, 94.3%] |
| OpenAI Math | 10/14<br>71.4% [45.4%, 88.3%] | 8/9<br>88.9% [56.5%, 98.0%] | 16/22<br>72.7% [51.8%, 86.8%] | 10/20<br>50.0% [29.9%, 70.1%] |

## All libraries

Full-pass reference: **30 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 100 | 0/1 | 14/100 | 10 | 10 | 71.4% [45.4%, 88.3%] | $4.72 / $10.12 |
| Sol | 100 | 0/1 | 9/100 | 8 | 8 | 88.9% [56.5%, 98.0%] | $1.32 / $4.38 |
| Sonnet | 130 | 0/1 | 52/130 | 34 | 34 | 65.4% [51.8%, 76.8%] | $5.93 / $3.42 |
| Luna | 130 | 0/1 | 50/130 | 21 | 21 | 42.0% [29.4%, 55.8%] | $0.24 / $0.14 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Opus | — | 0.50 [—]; n=9 | 0.65 [0.15, 1.00]; n=14 | 0.41 [-0.17, 0.86]; n=14 |
| Sol | 0.50 [—]; n=9 | — | 0.66 [—]; n=9 | 0.50 [—]; n=9 |
| Sonnet | 0.65 [0.15, 1.00]; n=14 | 0.66 [—]; n=9 | — | 0.47 [0.25, 0.66]; n=50 |
| Luna | 0.41 [-0.17, 0.86]; n=14 | 0.50 [—]; n=9 | 0.47 [0.25, 0.66]; n=50 | — |

Coverage annotations: Opus: 0 partial, 1 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 1 not applicable; Luna: 0 partial, 0 not applicable.

## Mathlib

Full-pass reference: **10 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sol | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sonnet | 10 | 1/1 | 10/10 | 6 | 6 | 60.0% [31.3%, 83.2%] | $1.04 / $1.04 |
| Luna | 10 | 1/1 | 10/10 | 2 | 2 | 20.0% [5.7%, 51.0%] | $0.05 / $0.05 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Opus | — | — | — | — |
| Sol | — | — | — | — |
| Sonnet | — | — | — | -0.10 [—]; n=10 |
| Luna | — | — | -0.10 [—]; n=10 | — |

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 0 not applicable; Luna: 0 partial, 0 not applicable.

## Tau Ceti

Full-pass reference: **10 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sol | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sonnet | 10 | 1/1 | 10/10 | 3 | 3 | 30.0% [10.8%, 60.3%] | $0.66 / $0.66 |
| Luna | 10 | 1/1 | 10/10 | 1 | 1 | 10.0% [1.8%, 40.4%] | $0.04 / $0.04 |

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
| Sonnet | 10 | 1/1 | 10/10 | 9 | 9 | 90.0% [59.6%, 98.2%] | $1.37 / $1.37 |
| Luna | 10 | 1/1 | 10/10 | 8 | 8 | 80.0% [49.0%, 94.3%] | $0.06 / $0.06 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Opus | — | — | — | — |
| Sol | — | — | — | — |
| Sonnet | — | — | — | 0.67 [—]; n=10 |
| Luna | — | — | 0.67 [—]; n=10 | — |

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 0 not applicable; Luna: 0 partial, 0 not applicable.

## OpenAI Math

Full-pass reference: **0 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 100 | 0/1 | 14/100 | 10 | 10 | 71.4% [45.4%, 88.3%] | $4.72 / $0.00 |
| Sol | 100 | 0/1 | 9/100 | 8 | 8 | 88.9% [56.5%, 98.0%] | $1.32 / $0.00 |
| Sonnet | 100 | 0/1 | 22/100 | 16 | 16 | 72.7% [51.8%, 86.8%] | $2.86 / $0.00 |
| Luna | 100 | 0/1 | 20/100 | 10 | 10 | 50.0% [29.9%, 70.1%] | $0.09 / $0.00 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Opus | — | 0.50 [—]; n=9 | 0.65 [0.06, 1.00]; n=14 | 0.41 [-0.18, 0.85]; n=14 |
| Sol | 0.50 [—]; n=9 | — | 0.66 [—]; n=9 | 0.50 [—]; n=9 |
| Sonnet | 0.65 [0.06, 1.00]; n=14 | 0.66 [—]; n=9 | — | 0.65 [0.41, 0.90]; n=20 |
| Luna | 0.41 [-0.18, 0.85]; n=14 | 0.50 [—]; n=9 | 0.65 [0.41, 0.90]; n=20 | — |

Coverage annotations: Opus: 0 partial, 1 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 1 not applicable; Luna: 0 partial, 0 not applicable.
