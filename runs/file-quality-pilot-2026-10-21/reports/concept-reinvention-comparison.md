# concept-reinvention

Generated 2026-10-21T07:24:42+00:00 · [Methods and notation](../../../AUDIT_METHODS.md) · 2,000 bootstrap draws.

## Library comparison

| Library | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Mathlib | — | — | 2/10<br>20.0% [5.7%, 51.0%] | 0/10<br>0.0% [0.0%, 27.8%] | — |
| Tau Ceti | — | — | 0/10<br>0.0% [0.0%, 27.8%] | 0/10<br>0.0% [0.0%, 27.8%] | — |
| Lean Pool | — | — | 4/10<br>40.0% [16.8%, 68.7%] | 0/10<br>0.0% [0.0%, 27.8%] | — |
| OpenAI Math | 2/20<br>10.0% [2.8%, 30.1%] | 1/16<br>6.2% [1.1%, 28.3%] | 3/29<br>10.3% [3.6%, 26.4%] | 3/26<br>11.5% [4.0%, 29.0%] | — |

## All libraries

Full-pass reference: **30 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 100 | 0/1 | 20/100 | 2 | 2 | 10.0% [2.8%, 30.1%] | $2.85 / $4.28 |
| Sol | 100 | 0/1 | 16/100 | 1 | 1 | 6.2% [1.1%, 28.3%] | $1.50 / $2.81 |
| Sonnet | 130 | 0/1 | 59/130 | 9 | 9 | 15.3% [8.2%, 26.5%] | $4.49 / $2.28 |
| Luna | 130 | 0/1 | 56/130 | 3 | 3 | 5.4% [1.8%, 14.6%] | $0.29 / $0.16 |
| DeepSeek | 40 | 0/1 | 0/40 | 0 | 0 | — | $0.00 / — |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | 0.68 [—]; n=16 | 1.00 [—]; n=20 | 0.69 [—]; n=20 | — |
| Sol | 0.68 [—]; n=16 | — | 0.68 [—]; n=16 | 1.00 [—]; n=16 | — |
| Sonnet | 1.00 [—]; n=20 | 0.68 [—]; n=16 | — | 0.11 [—]; n=56 | — |
| Luna | 0.69 [—]; n=20 | 1.00 [—]; n=16 | 0.11 [—]; n=56 | — | — |
| DeepSeek | — | — | — | — | — |

Coverage annotations: Opus: 0 partial, 9 not applicable; Sol: 0 partial, 3 not applicable; Sonnet: 0 partial, 14 not applicable; Luna: 0 partial, 0 not applicable; DeepSeek: 0 partial, 0 not applicable.

## Mathlib

Full-pass reference: **10 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sol | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sonnet | 10 | 1/1 | 10/10 | 2 | 2 | 20.0% [5.7%, 51.0%] | $0.71 / $0.71 |
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

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 1 not applicable; Luna: 0 partial, 0 not applicable; DeepSeek: 0 partial, 0 not applicable.

## Tau Ceti

Full-pass reference: **10 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sol | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sonnet | 10 | 1/1 | 10/10 | 0 | 0 | 0.0% [0.0%, 27.8%] | $0.39 / $0.39 |
| Luna | 10 | 1/1 | 10/10 | 0 | 0 | 0.0% [0.0%, 27.8%] | $0.04 / $0.04 |
| DeepSeek | 10 | 0/1 | 0/10 | 0 | 0 | — | $0.00 / — |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | — | — | — | — |
| Sol | — | — | — | — | — |
| Sonnet | — | — | — | —; n=10 | — |
| Luna | — | — | —; n=10 | — | — |
| DeepSeek | — | — | — | — | — |

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 3 not applicable; Luna: 0 partial, 0 not applicable; DeepSeek: 0 partial, 0 not applicable.

## Lean Pool

Full-pass reference: **10 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sol | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sonnet | 10 | 1/1 | 10/10 | 4 | 4 | 40.0% [16.8%, 68.7%] | $1.10 / $1.10 |
| Luna | 10 | 1/1 | 10/10 | 0 | 0 | 0.0% [0.0%, 27.8%] | $0.06 / $0.06 |
| DeepSeek | 10 | 0/1 | 0/10 | 0 | 0 | — | $0.00 / — |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | — | — | — | — |
| Sol | — | — | — | — | — |
| Sonnet | — | — | — | —; n=10 | — |
| Luna | — | — | —; n=10 | — | — |
| DeepSeek | — | — | — | — | — |

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 1 not applicable; Luna: 0 partial, 0 not applicable; DeepSeek: 0 partial, 0 not applicable.

## OpenAI Math

Full-pass reference: **0 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 100 | 0/1 | 20/100 | 2 | 2 | 10.0% [2.8%, 30.1%] | $2.85 / $0.00 |
| Sol | 100 | 0/1 | 16/100 | 1 | 1 | 6.2% [1.1%, 28.3%] | $1.50 / $0.00 |
| Sonnet | 100 | 0/1 | 29/100 | 3 | 3 | 10.3% [3.6%, 26.4%] | $2.30 / $0.00 |
| Luna | 100 | 0/1 | 26/100 | 3 | 3 | 11.5% [4.0%, 29.0%] | $0.14 / $0.00 |
| DeepSeek | 10 | 0/1 | 0/10 | 0 | 0 | — | $0.00 / — |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | 0.68 [—]; n=16 | 1.00 [—]; n=20 | 0.69 [—]; n=20 | — |
| Sol | 0.68 [—]; n=16 | — | 0.68 [—]; n=16 | 1.00 [—]; n=16 | — |
| Sonnet | 1.00 [—]; n=20 | 0.68 [—]; n=16 | — | 0.25 [—]; n=26 | — |
| Luna | 0.69 [—]; n=20 | 1.00 [—]; n=16 | 0.25 [—]; n=26 | — | — |
| DeepSeek | — | — | — | — | — |

Coverage annotations: Opus: 0 partial, 9 not applicable; Sol: 0 partial, 3 not applicable; Sonnet: 0 partial, 9 not applicable; Luna: 0 partial, 0 not applicable; DeepSeek: 0 partial, 0 not applicable.
