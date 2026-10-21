# statement-generality

Generated 2026-10-21T11:05:05+00:00 · [Methods and notation](../../../AUDIT_METHODS.md) · 2,000 bootstrap draws.

## Library comparison

| Library | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Mathlib | — | — | 6/10<br>60.0% [31.3%, 83.2%] | 2/10<br>20.0% [5.7%, 51.0%] | — |
| Tau Ceti | — | — | 3/10<br>30.0% [10.8%, 60.3%] | 1/10<br>10.0% [1.8%, 40.4%] | — |
| Lean Pool | — | — | 9/10<br>90.0% [59.6%, 98.2%] | 8/10<br>80.0% [49.0%, 94.3%] | — |
| OpenAI Math | 16/22<br>72.7% [51.8%, 86.8%] | 56/70<br>80.0% [69.2%, 87.7%] | 27/40<br>67.5% [52.0%, 79.9%] | 24/48<br>50.0% [36.4%, 63.6%] | — |

## All libraries

Full-pass reference: **30 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 100 | 0/1 | 22/100 | 16 | 16 | 72.7% [51.8%, 86.8%] | $7.60 / $10.37 |
| Sol | 100 | 0/1 | 70/100 | 56 | 56 | 80.0% [69.2%, 87.7%] | $9.35 / $4.01 |
| Sonnet | 130 | 0/1 | 70/130 | 45 | 45 | 64.3% [52.6%, 74.5%] | $7.96 / $3.41 |
| Luna | 130 | 0/1 | 78/130 | 35 | 35 | 44.9% [34.3%, 55.9%] | $0.38 / $0.14 |
| DeepSeek | 40 | 0/1 | 0/40 | 0 | 0 | — | $0.00 / — |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | 0.24 [-0.22, 0.70]; n=22 | 0.54 [0.05, 0.90]; n=22 | 0.41 [0.01, 0.73]; n=22 | — |
| Sol | 0.24 [-0.22, 0.70]; n=22 | — | 0.65 [0.37, 0.87]; n=40 | 0.37 [0.13, 0.58]; n=48 | — |
| Sonnet | 0.54 [0.05, 0.90]; n=22 | 0.65 [0.37, 0.87]; n=40 | — | 0.46 [0.28, 0.63]; n=70 | — |
| Luna | 0.41 [0.01, 0.73]; n=22 | 0.37 [0.13, 0.58]; n=48 | 0.46 [0.28, 0.63]; n=70 | — | — |
| DeepSeek | — | — | — | — | — |

Coverage annotations: Opus: 0 partial, 1 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 1 not applicable; Luna: 0 partial, 0 not applicable; DeepSeek: 0 partial, 0 not applicable.

## Mathlib

Full-pass reference: **10 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sol | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sonnet | 10 | 1/1 | 10/10 | 6 | 6 | 60.0% [31.3%, 83.2%] | $1.04 / $1.04 |
| Luna | 10 | 1/1 | 10/10 | 2 | 2 | 20.0% [5.7%, 51.0%] | $0.05 / $0.05 |
| DeepSeek | 10 | 0/1 | 0/10 | 0 | 0 | — | $0.00 / — |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | — | — | — | — |
| Sol | — | — | — | — | — |
| Sonnet | — | — | — | -0.10 [—]; n=10 | — |
| Luna | — | — | -0.10 [—]; n=10 | — | — |
| DeepSeek | — | — | — | — | — |

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 0 not applicable; Luna: 0 partial, 0 not applicable; DeepSeek: 0 partial, 0 not applicable.

## Tau Ceti

Full-pass reference: **10 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sol | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sonnet | 10 | 1/1 | 10/10 | 3 | 3 | 30.0% [10.8%, 60.3%] | $0.66 / $0.66 |
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

## Lean Pool

Full-pass reference: **10 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sol | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sonnet | 10 | 1/1 | 10/10 | 9 | 9 | 90.0% [59.6%, 98.2%] | $1.37 / $1.37 |
| Luna | 10 | 1/1 | 10/10 | 8 | 8 | 80.0% [49.0%, 94.3%] | $0.06 / $0.06 |
| DeepSeek | 10 | 0/1 | 0/10 | 0 | 0 | — | $0.00 / — |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | — | — | — | — |
| Sol | — | — | — | — | — |
| Sonnet | — | — | — | 0.67 [—]; n=10 | — |
| Luna | — | — | 0.67 [—]; n=10 | — | — |
| DeepSeek | — | — | — | — | — |

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 0 not applicable; Luna: 0 partial, 0 not applicable; DeepSeek: 0 partial, 0 not applicable.

## OpenAI Math

Full-pass reference: **0 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 100 | 0/1 | 22/100 | 16 | 16 | 72.7% [51.8%, 86.8%] | $7.60 / $0.00 |
| Sol | 100 | 0/1 | 70/100 | 56 | 56 | 80.0% [69.2%, 87.7%] | $9.35 / $0.00 |
| Sonnet | 100 | 0/1 | 40/100 | 27 | 27 | 67.5% [52.0%, 79.9%] | $4.90 / $0.00 |
| Luna | 100 | 0/1 | 48/100 | 24 | 24 | 50.0% [36.4%, 63.6%] | $0.23 / $0.00 |
| DeepSeek | 10 | 0/1 | 0/10 | 0 | 0 | — | $0.00 / — |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | 0.24 [-0.22, 0.69]; n=22 | 0.54 [0.10, 0.90]; n=22 | 0.41 [0.00, 0.72]; n=22 | — |
| Sol | 0.24 [-0.22, 0.69]; n=22 | — | 0.65 [0.38, 0.89]; n=40 | 0.37 [0.13, 0.58]; n=48 | — |
| Sonnet | 0.54 [0.10, 0.90]; n=22 | 0.65 [0.38, 0.89]; n=40 | — | 0.55 [0.31, 0.77]; n=40 | — |
| Luna | 0.41 [0.00, 0.72]; n=22 | 0.37 [0.13, 0.58]; n=48 | 0.55 [0.31, 0.77]; n=40 | — | — |
| DeepSeek | — | — | — | — | — |

Coverage annotations: Opus: 0 partial, 1 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 1 not applicable; Luna: 0 partial, 0 not applicable; DeepSeek: 0 partial, 0 not applicable.
