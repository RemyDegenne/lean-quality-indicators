# vacuity-and-misstatement

Generated 2026-10-21T07:24:42+00:00 · [Methods and notation](../../../AUDIT_METHODS.md) · 2,000 bootstrap draws.

## Library comparison

| Library | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Mathlib | — | — | 3/10<br>30.0% [10.8%, 60.3%] | 1/10<br>10.0% [1.8%, 40.4%] | — |
| Tau Ceti | — | — | 0/10<br>0.0% [0.0%, 27.8%] | 1/10<br>10.0% [1.8%, 40.4%] | — |
| Lean Pool | — | — | 2/10<br>20.0% [5.7%, 51.0%] | 0/10<br>0.0% [0.0%, 27.8%] | — |
| OpenAI Math | 0/19<br>0.0% [0.0%, 16.8%] | 0/15<br>0.0% [0.0%, 20.4%] | 0/29<br>0.0% [0.0%, 11.7%] | 1/26<br>3.8% [0.7%, 18.9%] | — |

## All libraries

Full-pass reference: **30 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 100 | 0/1 | 19/100 | 0 | 0 | 0.0% [0.0%, 16.8%] | $4.28 / $6.76 |
| Sol | 100 | 0/1 | 15/100 | 0 | 0 | 0.0% [0.0%, 20.4%] | $1.35 / $2.69 |
| Sonnet | 130 | 0/1 | 59/130 | 5 | 5 | 8.5% [3.7%, 18.4%] | $5.11 / $2.60 |
| Luna | 130 | 0/1 | 56/130 | 3 | 3 | 5.4% [1.8%, 14.6%] | $0.26 / $0.14 |
| DeepSeek | 40 | 0/1 | 0/40 | 0 | 0 | — | $0.00 / — |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | —; n=15 | —; n=19 | —; n=19 | — |
| Sol | —; n=15 | — | —; n=15 | —; n=15 | — |
| Sonnet | —; n=19 | —; n=15 | — | -0.07 [—]; n=56 | — |
| Luna | —; n=19 | —; n=15 | -0.07 [—]; n=56 | — | — |
| DeepSeek | — | — | — | — | — |

Coverage annotations: Opus: 0 partial, 1 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 0 not applicable; Luna: 0 partial, 0 not applicable; DeepSeek: 0 partial, 0 not applicable.

## Mathlib

Full-pass reference: **10 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sol | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sonnet | 10 | 1/1 | 10/10 | 3 | 3 | 30.0% [10.8%, 60.3%] | $0.48 / $0.48 |
| Luna | 10 | 1/1 | 10/10 | 1 | 1 | 10.0% [1.8%, 40.4%] | $0.04 / $0.04 |
| DeepSeek | 10 | 0/1 | 0/10 | 0 | 0 | — | $0.00 / — |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | — | — | — | — |
| Sol | — | — | — | — | — |
| Sonnet | — | — | — | -0.22 [—]; n=10 | — |
| Luna | — | — | -0.22 [—]; n=10 | — | — |
| DeepSeek | — | — | — | — | — |

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 0 not applicable; Luna: 0 partial, 0 not applicable; DeepSeek: 0 partial, 0 not applicable.

## Tau Ceti

Full-pass reference: **10 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sol | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sonnet | 10 | 1/1 | 10/10 | 0 | 0 | 0.0% [0.0%, 27.8%] | $0.62 / $0.62 |
| Luna | 10 | 1/1 | 10/10 | 1 | 1 | 10.0% [1.8%, 40.4%] | $0.05 / $0.05 |
| DeepSeek | 10 | 0/1 | 0/10 | 0 | 0 | — | $0.00 / — |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | — | — | — | — |
| Sol | — | — | — | — | — |
| Sonnet | — | — | — | —; n=10 | — |
| Luna | — | — | —; n=10 | — | — |
| DeepSeek | — | — | — | — | — |

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 0 not applicable; Luna: 0 partial, 0 not applicable; DeepSeek: 0 partial, 0 not applicable.

## Lean Pool

Full-pass reference: **10 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sol | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sonnet | 10 | 1/1 | 10/10 | 2 | 2 | 20.0% [5.7%, 51.0%] | $1.14 / $1.14 |
| Luna | 10 | 1/1 | 10/10 | 0 | 0 | 0.0% [0.0%, 27.8%] | $0.05 / $0.05 |
| DeepSeek | 10 | 0/1 | 0/10 | 0 | 0 | — | $0.00 / — |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | — | — | — | — |
| Sol | — | — | — | — | — |
| Sonnet | — | — | — | —; n=10 | — |
| Luna | — | — | —; n=10 | — | — |
| DeepSeek | — | — | — | — | — |

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 0 not applicable; Luna: 0 partial, 0 not applicable; DeepSeek: 0 partial, 0 not applicable.

## OpenAI Math

Full-pass reference: **0 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 100 | 0/1 | 19/100 | 0 | 0 | 0.0% [0.0%, 16.8%] | $4.28 / $0.00 |
| Sol | 100 | 0/1 | 15/100 | 0 | 0 | 0.0% [0.0%, 20.4%] | $1.35 / $0.00 |
| Sonnet | 100 | 0/1 | 29/100 | 0 | 0 | 0.0% [0.0%, 11.7%] | $2.87 / $0.00 |
| Luna | 100 | 0/1 | 26/100 | 1 | 1 | 3.8% [0.7%, 18.9%] | $0.13 / $0.00 |
| DeepSeek | 10 | 0/1 | 0/10 | 0 | 0 | — | $0.00 / — |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | —; n=15 | —; n=19 | —; n=19 | — |
| Sol | —; n=15 | — | —; n=15 | —; n=15 | — |
| Sonnet | —; n=19 | —; n=15 | — | —; n=26 | — |
| Luna | —; n=19 | —; n=15 | —; n=26 | — | — |
| DeepSeek | — | — | — | — | — |

Coverage annotations: Opus: 0 partial, 1 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 0 not applicable; Luna: 0 partial, 0 not applicable; DeepSeek: 0 partial, 0 not applicable.
