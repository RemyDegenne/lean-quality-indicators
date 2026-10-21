# repeated-proof-machinery

Generated 2026-10-21T06:58:56+00:00 · [Methods and notation](../../../AUDIT_METHODS.md) · 2,000 bootstrap draws.

## Library comparison

| Library | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Mathlib | — | — | 2/10<br>20.0% [5.7%, 51.0%] | 2/10<br>20.0% [5.7%, 51.0%] |
| Tau Ceti | — | — | 2/10<br>20.0% [5.7%, 51.0%] | 0/10<br>0.0% [0.0%, 27.8%] |
| Lean Pool | — | — | 6/10<br>60.0% [31.3%, 83.2%] | 3/10<br>30.0% [10.8%, 60.3%] |
| OpenAI Math | 6/14<br>42.9% [21.4%, 67.4%] | 1/9<br>11.1% [2.0%, 43.5%] | 7/22<br>31.8% [16.4%, 52.7%] | 3/20<br>15.0% [5.2%, 36.0%] |

## All libraries

Full-pass reference: **30 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 100 | 0/1 | 14/100 | 6 | 6 | 42.9% [21.4%, 67.4%] | $3.67 / $7.87 |
| Sol | 100 | 0/1 | 9/100 | 1 | 1 | 11.1% [2.0%, 43.5%] | $0.86 / $2.87 |
| Sonnet | 130 | 0/1 | 52/130 | 17 | 17 | 32.7% [21.5%, 46.2%] | $3.73 / $2.15 |
| Luna | 130 | 0/1 | 50/130 | 8 | 8 | 16.0% [8.3%, 28.5%] | $0.18 / $0.11 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Opus | — | 0.32 [—]; n=9 | 0.56 [0.06, 1.00]; n=14 | 0.60 [—]; n=14 |
| Sol | 0.32 [—]; n=9 | — | 0.50 [—]; n=9 | 0.66 [—]; n=9 |
| Sonnet | 0.56 [0.06, 1.00]; n=14 | 0.50 [—]; n=9 | — | 0.55 [0.29, 0.77]; n=50 |
| Luna | 0.60 [—]; n=14 | 0.66 [—]; n=9 | 0.55 [0.29, 0.77]; n=50 | — |

Coverage annotations: Opus: 0 partial, 1 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 2 not applicable; Luna: 0 partial, 0 not applicable.

## Mathlib

Full-pass reference: **10 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sol | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sonnet | 10 | 1/1 | 10/10 | 2 | 2 | 20.0% [5.7%, 51.0%] | $0.55 / $0.55 |
| Luna | 10 | 1/1 | 10/10 | 2 | 2 | 20.0% [5.7%, 51.0%] | $0.03 / $0.03 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Opus | — | — | — | — |
| Sol | — | — | — | — |
| Sonnet | — | — | — | 1.00 [—]; n=10 |
| Luna | — | — | 1.00 [—]; n=10 | — |

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 1 not applicable; Luna: 0 partial, 0 not applicable.

## Tau Ceti

Full-pass reference: **10 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sol | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sonnet | 10 | 1/1 | 10/10 | 2 | 2 | 20.0% [5.7%, 51.0%] | $0.46 / $0.46 |
| Luna | 10 | 1/1 | 10/10 | 0 | 0 | 0.0% [0.0%, 27.8%] | $0.03 / $0.03 |

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
| Sonnet | 10 | 1/1 | 10/10 | 6 | 6 | 60.0% [31.3%, 83.2%] | $1.05 / $1.05 |
| Luna | 10 | 1/1 | 10/10 | 3 | 3 | 30.0% [10.8%, 60.3%] | $0.04 / $0.04 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Opus | — | — | — | — |
| Sol | — | — | — | — |
| Sonnet | — | — | — | 0.53 [—]; n=10 |
| Luna | — | — | 0.53 [—]; n=10 | — |

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 0 not applicable; Luna: 0 partial, 0 not applicable.

## OpenAI Math

Full-pass reference: **0 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 100 | 0/1 | 14/100 | 6 | 6 | 42.9% [21.4%, 67.4%] | $3.67 / $0.00 |
| Sol | 100 | 0/1 | 9/100 | 1 | 1 | 11.1% [2.0%, 43.5%] | $0.86 / $0.00 |
| Sonnet | 100 | 0/1 | 22/100 | 7 | 7 | 31.8% [16.4%, 52.7%] | $1.66 / $0.00 |
| Luna | 100 | 0/1 | 20/100 | 3 | 3 | 15.0% [5.2%, 36.0%] | $0.07 / $0.00 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Opus | — | 0.32 [—]; n=9 | 0.56 [0.07, 1.00]; n=14 | 0.60 [—]; n=14 |
| Sol | 0.32 [—]; n=9 | — | 0.50 [—]; n=9 | 0.66 [—]; n=9 |
| Sonnet | 0.56 [0.07, 1.00]; n=14 | 0.50 [—]; n=9 | — | 0.40 [—]; n=20 |
| Luna | 0.60 [—]; n=14 | 0.66 [—]; n=9 | 0.40 [—]; n=20 | — |

Coverage annotations: Opus: 0 partial, 1 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 1 not applicable; Luna: 0 partial, 0 not applicable.
