# repeated-proof-machinery

Generated 2026-10-21T07:24:42+00:00 · [Methods and notation](../../../AUDIT_METHODS.md) · 2,000 bootstrap draws.

## Library comparison

| Library | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Mathlib | — | — | 2/10<br>20.0% [5.7%, 51.0%] | 2/10<br>20.0% [5.7%, 51.0%] | — |
| Tau Ceti | — | — | 2/10<br>20.0% [5.7%, 51.0%] | 0/10<br>0.0% [0.0%, 27.8%] | — |
| Lean Pool | — | — | 6/10<br>60.0% [31.3%, 83.2%] | 3/10<br>30.0% [10.8%, 60.3%] | — |
| OpenAI Math | 6/19<br>31.6% [15.4%, 54.0%] | 2/15<br>13.3% [3.7%, 37.9%] | 11/28<br>39.3% [23.6%, 57.6%] | 5/25<br>20.0% [8.9%, 39.1%] | — |

## All libraries

Full-pass reference: **30 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 100 | 0/1 | 19/100 | 6 | 6 | 31.6% [15.4%, 54.0%] | $4.42 / $6.98 |
| Sol | 100 | 0/1 | 15/100 | 2 | 2 | 13.3% [3.7%, 37.9%] | $1.27 / $2.54 |
| Sonnet | 130 | 0/1 | 58/130 | 21 | 21 | 36.2% [25.1%, 49.1%] | $4.35 / $2.25 |
| Luna | 130 | 0/1 | 55/130 | 10 | 10 | 18.2% [10.2%, 30.3%] | $0.20 / $0.11 |
| DeepSeek | 40 | 0/1 | 0/40 | 0 | 0 | — | $0.00 / — |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | 0.48 [—]; n=15 | 0.62 [0.19, 1.00]; n=19 | 0.64 [—]; n=19 | — |
| Sol | 0.48 [—]; n=15 | — | 0.55 [—]; n=15 | 0.78 [—]; n=15 | — |
| Sonnet | 0.62 [0.19, 1.00]; n=19 | 0.55 [—]; n=15 | — | 0.55 [0.31, 0.75]; n=55 | — |
| Luna | 0.64 [—]; n=19 | 0.78 [—]; n=15 | 0.55 [0.31, 0.75]; n=55 | — | — |
| DeepSeek | — | — | — | — | — |

Coverage annotations: Opus: 0 partial, 1 not applicable; Sol: 0 partial, 1 not applicable; Sonnet: 0 partial, 2 not applicable; Luna: 0 partial, 0 not applicable; DeepSeek: 0 partial, 0 not applicable.

## Mathlib

Full-pass reference: **10 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sol | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sonnet | 10 | 1/1 | 10/10 | 2 | 2 | 20.0% [5.7%, 51.0%] | $0.55 / $0.55 |
| Luna | 10 | 1/1 | 10/10 | 2 | 2 | 20.0% [5.7%, 51.0%] | $0.03 / $0.03 |
| DeepSeek | 10 | 0/1 | 0/10 | 0 | 0 | — | $0.00 / — |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | — | — | — | — |
| Sol | — | — | — | — | — |
| Sonnet | — | — | — | 1.00 [—]; n=10 | — |
| Luna | — | — | 1.00 [—]; n=10 | — | — |
| DeepSeek | — | — | — | — | — |

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 1 not applicable; Luna: 0 partial, 0 not applicable; DeepSeek: 0 partial, 0 not applicable.

## Tau Ceti

Full-pass reference: **10 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sol | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sonnet | 10 | 1/1 | 10/10 | 2 | 2 | 20.0% [5.7%, 51.0%] | $0.46 / $0.46 |
| Luna | 10 | 1/1 | 10/10 | 0 | 0 | 0.0% [0.0%, 27.8%] | $0.03 / $0.03 |
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
| Sonnet | 10 | 1/1 | 10/10 | 6 | 6 | 60.0% [31.3%, 83.2%] | $1.05 / $1.05 |
| Luna | 10 | 1/1 | 10/10 | 3 | 3 | 30.0% [10.8%, 60.3%] | $0.04 / $0.04 |
| DeepSeek | 10 | 0/1 | 0/10 | 0 | 0 | — | $0.00 / — |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | — | — | — | — |
| Sol | — | — | — | — | — |
| Sonnet | — | — | — | 0.53 [—]; n=10 | — |
| Luna | — | — | 0.53 [—]; n=10 | — | — |
| DeepSeek | — | — | — | — | — |

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 0 not applicable; Luna: 0 partial, 0 not applicable; DeepSeek: 0 partial, 0 not applicable.

## OpenAI Math

Full-pass reference: **0 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 100 | 0/1 | 19/100 | 6 | 6 | 31.6% [15.4%, 54.0%] | $4.42 / $0.00 |
| Sol | 100 | 0/1 | 15/100 | 2 | 2 | 13.3% [3.7%, 37.9%] | $1.27 / $0.00 |
| Sonnet | 100 | 0/1 | 28/100 | 11 | 11 | 39.3% [23.6%, 57.6%] | $2.29 / $0.00 |
| Luna | 100 | 0/1 | 25/100 | 5 | 5 | 20.0% [8.9%, 39.1%] | $0.09 / $0.00 |
| DeepSeek | 10 | 0/1 | 0/10 | 0 | 0 | — | $0.00 / — |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | 0.48 [—]; n=15 | 0.62 [0.14, 1.00]; n=19 | 0.64 [—]; n=19 | — |
| Sol | 0.48 [—]; n=15 | — | 0.55 [—]; n=15 | 0.78 [—]; n=15 | — |
| Sonnet | 0.62 [0.14, 1.00]; n=19 | 0.55 [—]; n=15 | — | 0.46 [0.04, 0.80]; n=25 | — |
| Luna | 0.64 [—]; n=19 | 0.78 [—]; n=15 | 0.46 [0.04, 0.80]; n=25 | — | — |
| DeepSeek | — | — | — | — | — |

Coverage annotations: Opus: 0 partial, 1 not applicable; Sol: 0 partial, 1 not applicable; Sonnet: 0 partial, 1 not applicable; Luna: 0 partial, 0 not applicable; DeepSeek: 0 partial, 0 not applicable.
