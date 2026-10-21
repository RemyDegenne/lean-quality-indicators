# readable-proof-simplification

Generated 2026-10-21T11:05:05+00:00 · [Methods and notation](../../../AUDIT_METHODS.md) · 2,000 bootstrap draws.

## Library comparison

| Library | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Mathlib | — | — | 7/10<br>70.0% [39.7%, 89.2%] | 2/10<br>20.0% [5.7%, 51.0%] | — |
| Tau Ceti | — | — | 8/10<br>80.0% [49.0%, 94.3%] | 3/10<br>30.0% [10.8%, 60.3%] | — |
| Lean Pool | — | — | 9/10<br>90.0% [59.6%, 98.2%] | 6/10<br>60.0% [31.3%, 83.2%] | — |
| OpenAI Math | 18/22<br>81.8% [61.5%, 92.7%] | 55/68<br>80.9% [70.0%, 88.5%] | 31/40<br>77.5% [62.5%, 87.7%] | 9/47<br>19.1% [10.4%, 32.5%] | — |

## All libraries

Full-pass reference: **30 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 100 | 0/1 | 22/100 | 18 | 18 | 81.8% [61.5%, 92.7%] | $7.53 / $10.27 |
| Sol | 100 | 0/1 | 68/100 | 55 | 55 | 80.9% [70.0%, 88.5%] | $8.70 / $3.84 |
| Sonnet | 130 | 0/1 | 70/130 | 55 | 55 | 78.6% [67.6%, 86.6%] | $9.36 / $4.01 |
| Luna | 130 | 0/1 | 77/130 | 20 | 20 | 26.0% [17.5%, 36.7%] | $0.31 / $0.12 |
| DeepSeek | 40 | 0/1 | 0/40 | 0 | 0 | — | $0.00 / — |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | 0.44 [-0.10, 0.79]; n=22 | 0.59 [-0.05, 1.00]; n=22 | 0.26 [0.10, 0.43]; n=22 | — |
| Sol | 0.44 [-0.10, 0.79]; n=22 | — | 0.52 [0.17, 0.81]; n=40 | -0.11 [-0.42, 0.19]; n=47 | — |
| Sonnet | 0.59 [-0.05, 1.00]; n=22 | 0.52 [0.17, 0.81]; n=40 | — | 0.23 [0.04, 0.36]; n=70 | — |
| Luna | 0.26 [0.10, 0.43]; n=22 | -0.11 [-0.42, 0.19]; n=47 | 0.23 [0.04, 0.36]; n=70 | — | — |
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
| Opus | 100 | 0/1 | 22/100 | 18 | 18 | 81.8% [61.5%, 92.7%] | $7.53 / $0.00 |
| Sol | 100 | 0/1 | 68/100 | 55 | 55 | 80.9% [70.0%, 88.5%] | $8.70 / $0.00 |
| Sonnet | 100 | 0/1 | 40/100 | 31 | 31 | 77.5% [62.5%, 87.7%] | $5.84 / $0.00 |
| Luna | 100 | 0/1 | 47/100 | 9 | 9 | 19.1% [10.4%, 32.5%] | $0.19 / $0.00 |
| DeepSeek | 10 | 0/1 | 0/10 | 0 | 0 | — | $0.00 / — |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | 0.44 [-0.09, 0.81]; n=22 | 0.59 [0.10, 1.00]; n=22 | 0.26 [0.10, 0.42]; n=22 | — |
| Sol | 0.44 [-0.09, 0.81]; n=22 | — | 0.52 [0.18, 0.81]; n=40 | -0.11 [-0.45, 0.19]; n=47 | — |
| Sonnet | 0.59 [0.10, 1.00]; n=22 | 0.52 [0.18, 0.81]; n=40 | — | 0.09 [-0.22, 0.32]; n=40 | — |
| Luna | 0.26 [0.10, 0.42]; n=22 | -0.11 [-0.45, 0.19]; n=47 | 0.09 [-0.22, 0.32]; n=40 | — | — |
| DeepSeek | — | — | — | — | — |

Coverage annotations: Opus: 0 partial, 1 not applicable; Sol: 0 partial, 1 not applicable; Sonnet: 0 partial, 1 not applicable; Luna: 0 partial, 1 not applicable; DeepSeek: 0 partial, 0 not applicable.
