# simp-interface

Generated 2026-10-21T07:24:42+00:00 · [Methods and notation](../../../AUDIT_METHODS.md) · 2,000 bootstrap draws.

## Library comparison

| Library | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Mathlib | — | — | 4/10<br>40.0% [16.8%, 68.7%] | 4/10<br>40.0% [16.8%, 68.7%] | — |
| Tau Ceti | — | — | 3/10<br>30.0% [10.8%, 60.3%] | 1/10<br>10.0% [1.8%, 40.4%] | — |
| Lean Pool | — | — | 6/10<br>60.0% [31.3%, 83.2%] | 6/10<br>60.0% [31.3%, 83.2%] | — |
| OpenAI Math | 11/19<br>57.9% [36.3%, 76.9%] | 4/15<br>26.7% [10.9%, 52.0%] | 15/28<br>53.6% [35.8%, 70.5%] | 8/25<br>32.0% [17.2%, 51.6%] | — |

## All libraries

Full-pass reference: **30 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 100 | 0/1 | 19/100 | 11 | 11 | 57.9% [36.3%, 76.9%] | $5.49 / $8.66 |
| Sol | 100 | 0/1 | 15/100 | 4 | 4 | 26.7% [10.9%, 52.0%] | $1.51 / $3.03 |
| Sonnet | 130 | 0/1 | 58/130 | 28 | 28 | 48.3% [35.9%, 60.8%] | $5.12 / $2.65 |
| Luna | 130 | 0/1 | 55/130 | 19 | 19 | 34.5% [23.4%, 47.7%] | $0.26 / $0.14 |
| DeepSeek | 40 | 0/1 | 0/40 | 0 | 0 | — | $0.00 / — |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | 0.49 [0.22, 0.76]; n=15 | 0.69 [0.32, 1.00]; n=19 | 0.43 [-0.02, 0.76]; n=19 | — |
| Sol | 0.49 [0.22, 0.76]; n=15 | — | 0.49 [0.24, 0.76]; n=15 | 0.53 [-0.10, 1.00]; n=15 | — |
| Sonnet | 0.69 [0.32, 1.00]; n=19 | 0.49 [0.24, 0.76]; n=15 | — | 0.36 [0.11, 0.59]; n=55 | — |
| Luna | 0.43 [-0.02, 0.76]; n=19 | 0.53 [-0.10, 1.00]; n=15 | 0.36 [0.11, 0.59]; n=55 | — | — |
| DeepSeek | — | — | — | — | — |

Coverage annotations: Opus: 0 partial, 2 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 3 not applicable; Luna: 0 partial, 0 not applicable; DeepSeek: 0 partial, 0 not applicable.

## Mathlib

Full-pass reference: **10 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sol | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sonnet | 10 | 1/1 | 10/10 | 4 | 4 | 40.0% [16.8%, 68.7%] | $0.68 / $0.68 |
| Luna | 10 | 1/1 | 10/10 | 4 | 4 | 40.0% [16.8%, 68.7%] | $0.05 / $0.05 |
| DeepSeek | 10 | 0/1 | 0/10 | 0 | 0 | — | $0.00 / — |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | — | — | — | — |
| Sol | — | — | — | — | — |
| Sonnet | — | — | — | 0.58 [0.00, 1.00]; n=10 | — |
| Luna | — | — | 0.58 [0.00, 1.00]; n=10 | — | — |
| DeepSeek | — | — | — | — | — |

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 1 not applicable; Luna: 0 partial, 0 not applicable; DeepSeek: 0 partial, 0 not applicable.

## Tau Ceti

Full-pass reference: **10 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sol | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sonnet | 10 | 1/1 | 10/10 | 3 | 3 | 30.0% [10.8%, 60.3%] | $0.68 / $0.68 |
| Luna | 10 | 1/1 | 10/10 | 1 | 1 | 10.0% [1.8%, 40.4%] | $0.05 / $0.05 |
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

## Lean Pool

Full-pass reference: **10 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sol | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sonnet | 10 | 1/1 | 10/10 | 6 | 6 | 60.0% [31.3%, 83.2%] | $1.04 / $1.04 |
| Luna | 10 | 1/1 | 10/10 | 6 | 6 | 60.0% [31.3%, 83.2%] | $0.06 / $0.06 |
| DeepSeek | 10 | 0/1 | 0/10 | 0 | 0 | — | $0.00 / — |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | — | — | — | — |
| Sol | — | — | — | — | — |
| Sonnet | — | — | — | 0.58 [-0.17, 1.00]; n=10 | — |
| Luna | — | — | 0.58 [-0.17, 1.00]; n=10 | — | — |
| DeepSeek | — | — | — | — | — |

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 0 not applicable; Luna: 0 partial, 0 not applicable; DeepSeek: 0 partial, 0 not applicable.

## OpenAI Math

Full-pass reference: **0 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 100 | 0/1 | 19/100 | 11 | 11 | 57.9% [36.3%, 76.9%] | $5.49 / $0.00 |
| Sol | 100 | 0/1 | 15/100 | 4 | 4 | 26.7% [10.9%, 52.0%] | $1.51 / $0.00 |
| Sonnet | 100 | 0/1 | 28/100 | 15 | 15 | 53.6% [35.8%, 70.5%] | $2.73 / $0.00 |
| Luna | 100 | 0/1 | 25/100 | 8 | 8 | 32.0% [17.2%, 51.6%] | $0.11 / $0.00 |
| DeepSeek | 10 | 0/1 | 0/10 | 0 | 0 | — | $0.00 / — |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | 0.49 [0.24, 0.76]; n=15 | 0.69 [0.32, 1.00]; n=19 | 0.43 [0.03, 0.77]; n=19 | — |
| Sol | 0.49 [0.24, 0.76]; n=15 | — | 0.49 [0.24, 0.76]; n=15 | 0.53 [-0.07, 1.00]; n=15 | — |
| Sonnet | 0.69 [0.32, 1.00]; n=19 | 0.49 [0.24, 0.76]; n=15 | — | 0.26 [-0.13, 0.61]; n=25 | — |
| Luna | 0.43 [0.03, 0.77]; n=19 | 0.53 [-0.07, 1.00]; n=15 | 0.26 [-0.13, 0.61]; n=25 | — | — |
| DeepSeek | — | — | — | — | — |

Coverage annotations: Opus: 0 partial, 2 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 2 not applicable; Luna: 0 partial, 0 not applicable; DeepSeek: 0 partial, 0 not applicable.
