# vacuity-and-misstatement

Generated 2026-10-21T05:54:53+00:00 · [Methods and notation](../../../AUDIT_METHODS.md) · 2,000 bootstrap draws.

## Library comparison

| Library | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Mathlib | — | — | 3/10<br>30.0% [10.8%, 60.3%] | 1/10<br>10.0% [1.8%, 40.4%] |
| Tau Ceti | — | — | 0/10<br>0.0% [0.0%, 27.8%] | 1/10<br>10.0% [1.8%, 40.4%] |
| Lean Pool | — | — | 2/10<br>20.0% [5.7%, 51.0%] | 0/10<br>0.0% [0.0%, 27.8%] |
| OpenAI Math | 0/1<br>0.0% [0.0%, 79.3%] | 0/1<br>0.0% [0.0%, 79.3%] | 0/2<br>0.0% [0.0%, 65.8%] | 0/2<br>0.0% [0.0%, 65.8%] |

## All libraries

Full-pass reference: **30 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 100 | 0/1 | 1/100 | 0 | 0 | 0.0% [0.0%, 79.3%] | $0.20 / $6.07 |
| Sol | 100 | 0/1 | 1/100 | 0 | 0 | 0.0% [0.0%, 79.3%] | $0.14 / $4.16 |
| Sonnet | 130 | 0/1 | 32/130 | 5 | 5 | 15.6% [6.9%, 31.8%] | $2.42 / $2.27 |
| Luna | 130 | 0/1 | 32/130 | 2 | 2 | 6.2% [1.7%, 20.1%] | $0.14 / $0.13 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Opus | — | —; n=1 | —; n=1 | —; n=1 |
| Sol | —; n=1 | — | —; n=1 | —; n=1 |
| Sonnet | —; n=1 | —; n=1 | — | -0.11 [—]; n=32 |
| Luna | —; n=1 | —; n=1 | -0.11 [—]; n=32 | — |

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 0 not applicable; Luna: 0 partial, 0 not applicable.

## Mathlib

Full-pass reference: **10 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sol | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sonnet | 10 | 1/1 | 10/10 | 3 | 3 | 30.0% [10.8%, 60.3%] | $0.48 / $0.48 |
| Luna | 10 | 1/1 | 10/10 | 1 | 1 | 10.0% [1.8%, 40.4%] | $0.04 / $0.04 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Opus | — | — | — | — |
| Sol | — | — | — | — |
| Sonnet | — | — | — | -0.22 [—]; n=10 |
| Luna | — | — | -0.22 [—]; n=10 | — |

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 0 not applicable; Luna: 0 partial, 0 not applicable.

## Tau Ceti

Full-pass reference: **10 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sol | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sonnet | 10 | 1/1 | 10/10 | 0 | 0 | 0.0% [0.0%, 27.8%] | $0.62 / $0.62 |
| Luna | 10 | 1/1 | 10/10 | 1 | 1 | 10.0% [1.8%, 40.4%] | $0.05 / $0.05 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Opus | — | — | — | — |
| Sol | — | — | — | — |
| Sonnet | — | — | — | —; n=10 |
| Luna | — | — | —; n=10 | — |

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 0 not applicable; Luna: 0 partial, 0 not applicable.

## Lean Pool

Full-pass reference: **10 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sol | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sonnet | 10 | 1/1 | 10/10 | 2 | 2 | 20.0% [5.7%, 51.0%] | $1.14 / $1.14 |
| Luna | 10 | 1/1 | 10/10 | 0 | 0 | 0.0% [0.0%, 27.8%] | $0.05 / $0.05 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Opus | — | — | — | — |
| Sol | — | — | — | — |
| Sonnet | — | — | — | —; n=10 |
| Luna | — | — | —; n=10 | — |

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 0 not applicable; Luna: 0 partial, 0 not applicable.

## OpenAI Math

Full-pass reference: **0 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 100 | 0/1 | 1/100 | 0 | 0 | 0.0% [0.0%, 79.3%] | $0.20 / $0.00 |
| Sol | 100 | 0/1 | 1/100 | 0 | 0 | 0.0% [0.0%, 79.3%] | $0.14 / $0.00 |
| Sonnet | 100 | 0/1 | 2/100 | 0 | 0 | 0.0% [0.0%, 65.8%] | $0.17 / $0.00 |
| Luna | 100 | 0/1 | 2/100 | 0 | 0 | 0.0% [0.0%, 65.8%] | $0.01 / $0.00 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Opus | — | —; n=1 | —; n=1 | —; n=1 |
| Sol | —; n=1 | — | —; n=1 | —; n=1 |
| Sonnet | —; n=1 | —; n=1 | — | —; n=2 |
| Luna | —; n=1 | —; n=1 | —; n=2 | — |

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 0 not applicable; Luna: 0 partial, 0 not applicable.
