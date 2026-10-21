# concept-reinvention

Generated 2026-10-21T06:58:55+00:00 · [Methods and notation](../../../AUDIT_METHODS.md) · 2,000 bootstrap draws.

## Library comparison

| Library | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Mathlib | — | — | 2/10<br>20.0% [5.7%, 51.0%] | 0/10<br>0.0% [0.0%, 27.8%] |
| Tau Ceti | — | — | 0/10<br>0.0% [0.0%, 27.8%] | 0/10<br>0.0% [0.0%, 27.8%] |
| Lean Pool | — | — | 4/10<br>40.0% [16.8%, 68.7%] | 0/10<br>0.0% [0.0%, 27.8%] |
| OpenAI Math | 2/15<br>13.3% [3.7%, 37.9%] | 1/9<br>11.1% [2.0%, 43.5%] | 3/22<br>13.6% [4.7%, 33.3%] | 1/20<br>5.0% [0.9%, 23.6%] |

## All libraries

Full-pass reference: **30 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 100 | 0/1 | 15/100 | 2 | 2 | 13.3% [3.7%, 37.9%] | $2.19 / $4.37 |
| Sol | 100 | 0/1 | 9/100 | 1 | 1 | 11.1% [2.0%, 43.5%] | $0.80 / $2.65 |
| Sonnet | 130 | 0/1 | 52/130 | 9 | 9 | 17.3% [9.4%, 29.7%] | $3.90 / $2.25 |
| Luna | 130 | 0/1 | 50/130 | 1 | 1 | 2.0% [0.4%, 10.5%] | $0.26 / $0.15 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Opus | — | 1.00 [—]; n=9 | 1.00 [—]; n=15 | 0.68 [—]; n=15 |
| Sol | 1.00 [—]; n=9 | — | 1.00 [—]; n=9 | 1.00 [—]; n=9 |
| Sonnet | 1.00 [—]; n=15 | 1.00 [—]; n=9 | — | 0.33 [—]; n=50 |
| Luna | 0.68 [—]; n=15 | 1.00 [—]; n=9 | 0.33 [—]; n=50 | — |

Coverage annotations: Opus: 0 partial, 7 not applicable; Sol: 0 partial, 3 not applicable; Sonnet: 0 partial, 12 not applicable; Luna: 0 partial, 0 not applicable.

## Mathlib

Full-pass reference: **10 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sol | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sonnet | 10 | 1/1 | 10/10 | 2 | 2 | 20.0% [5.7%, 51.0%] | $0.71 / $0.71 |
| Luna | 10 | 1/1 | 10/10 | 0 | 0 | 0.0% [0.0%, 27.8%] | $0.05 / $0.05 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Opus | — | — | — | — |
| Sol | — | — | — | — |
| Sonnet | — | — | — | —; n=10 |
| Luna | — | — | —; n=10 | — |

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 1 not applicable; Luna: 0 partial, 0 not applicable.

## Tau Ceti

Full-pass reference: **10 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sol | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sonnet | 10 | 1/1 | 10/10 | 0 | 0 | 0.0% [0.0%, 27.8%] | $0.39 / $0.39 |
| Luna | 10 | 1/1 | 10/10 | 0 | 0 | 0.0% [0.0%, 27.8%] | $0.04 / $0.04 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Opus | — | — | — | — |
| Sol | — | — | — | — |
| Sonnet | — | — | — | —; n=10 |
| Luna | — | — | —; n=10 | — |

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 3 not applicable; Luna: 0 partial, 0 not applicable.

## Lean Pool

Full-pass reference: **10 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sol | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sonnet | 10 | 1/1 | 10/10 | 4 | 4 | 40.0% [16.8%, 68.7%] | $1.10 / $1.10 |
| Luna | 10 | 1/1 | 10/10 | 0 | 0 | 0.0% [0.0%, 27.8%] | $0.06 / $0.06 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Opus | — | — | — | — |
| Sol | — | — | — | — |
| Sonnet | — | — | — | —; n=10 |
| Luna | — | — | —; n=10 | — |

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 1 not applicable; Luna: 0 partial, 0 not applicable.

## OpenAI Math

Full-pass reference: **0 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 100 | 0/1 | 15/100 | 2 | 2 | 13.3% [3.7%, 37.9%] | $2.19 / $0.00 |
| Sol | 100 | 0/1 | 9/100 | 1 | 1 | 11.1% [2.0%, 43.5%] | $0.80 / $0.00 |
| Sonnet | 100 | 0/1 | 22/100 | 3 | 3 | 13.6% [4.7%, 33.3%] | $1.72 / $0.00 |
| Luna | 100 | 0/1 | 20/100 | 1 | 1 | 5.0% [0.9%, 23.6%] | $0.10 / $0.00 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Opus | — | 1.00 [—]; n=9 | 1.00 [—]; n=15 | 0.68 [—]; n=15 |
| Sol | 1.00 [—]; n=9 | — | 1.00 [—]; n=9 | 1.00 [—]; n=9 |
| Sonnet | 1.00 [—]; n=15 | 1.00 [—]; n=9 | — | 0.69 [—]; n=20 |
| Luna | 0.68 [—]; n=15 | 1.00 [—]; n=9 | 0.69 [—]; n=20 | — |

Coverage annotations: Opus: 0 partial, 7 not applicable; Sol: 0 partial, 3 not applicable; Sonnet: 0 partial, 7 not applicable; Luna: 0 partial, 0 not applicable.
