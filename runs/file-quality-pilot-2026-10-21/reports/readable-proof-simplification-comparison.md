# readable-proof-simplification

Generated 2026-10-22T00:03:29+00:00 · [Methods and notation](../../../AUDIT_METHODS.md) · 2,000 bootstrap draws.

## Library comparison

| Library | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Mathlib | — | — | 7/10<br>70.0% [39.7%, 89.2%] | 2/10<br>20.0% [5.7%, 51.0%] | 4/5<br>80.0% [37.6%, 96.4%] |
| Tau Ceti | — | — | 8/10<br>80.0% [49.0%, 94.3%] | 3/10<br>30.0% [10.8%, 60.3%] | 3/5<br>60.0% [23.1%, 88.2%] |
| Lean Pool | — | — | 9/10<br>90.0% [59.6%, 98.2%] | 6/10<br>60.0% [31.3%, 83.2%] | 4/5<br>80.0% [37.6%, 96.4%] |
| OpenAI Math | 84/100<br>84.0% [75.6%, 89.9%] | 82/100<br>82.0% [73.3%, 88.3%] | 78/100<br>78.0% [68.9%, 85.0%] | 25/100<br>25.0% [17.5%, 34.3%] | 4/5<br>80.0% [37.6%, 96.4%] |

## All libraries

Full-pass reference: **130 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 100 | 1/1 | 100/100 | 84 | 84 | 84.0% [75.6%, 89.9%] | $34.58 / $44.96 |
| Sol | 100 | 1/1 | 100/100 | 82 | 82 | 82.0% [73.3%, 88.3%] | $12.68 / $16.48 |
| Sonnet | 130 | 1/1 | 130/130 | 102 | 102 | 78.5% [70.6%, 84.7%] | $18.52 / $18.52 |
| Luna | 130 | 1/1 | 130/130 | 36 | 36 | 27.7% [20.7%, 35.9%] | $0.50 / $0.50 |
| DeepSeek | 40 | 0/1 | 20/40 | 15 | 15 | 75.0% [53.1%, 88.8%] | $0.57 / $3.74 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | 0.65 [0.42, 0.83]; n=100 | 0.49 [0.27, 0.69]; n=100 | 0.19 [0.04, 0.30]; n=100 | —; n=5 |
| Sol | 0.65 [0.42, 0.83]; n=100 | — | 0.38 [0.14, 0.59]; n=100 | 0.03 [-0.17, 0.20]; n=100 | 0.61 [—]; n=5 |
| Sonnet | 0.49 [0.27, 0.69]; n=100 | 0.38 [0.14, 0.59]; n=100 | — | 0.16 [0.01, 0.29]; n=130 | 0.73 [0.33, 1.00]; n=20 |
| Luna | 0.19 [0.04, 0.30]; n=100 | 0.03 [-0.17, 0.20]; n=100 | 0.16 [0.01, 0.29]; n=130 | — | 0.29 [0.13, 0.47]; n=20 |
| DeepSeek | —; n=5 | 0.61 [—]; n=5 | 0.73 [0.33, 1.00]; n=20 | 0.29 [0.13, 0.47]; n=20 | — |

Coverage annotations: Opus: 0 partial, 1 not applicable; Sol: 0 partial, 1 not applicable; Sonnet: 0 partial, 1 not applicable; Luna: 0 partial, 1 not applicable; DeepSeek: 0 partial, 0 not applicable.

## Mathlib

Full-pass reference: **10 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sol | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sonnet | 10 | 1/1 | 10/10 | 7 | 7 | 70.0% [39.7%, 89.2%] | $0.91 / $0.91 |
| Luna | 10 | 1/1 | 10/10 | 2 | 2 | 20.0% [5.7%, 51.0%] | $0.03 / $0.03 |
| DeepSeek | 10 | 0/1 | 5/10 | 4 | 4 | 80.0% [37.6%, 96.4%] | $0.16 / $0.32 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | — | — | — | — |
| Sol | — | — | — | — | — |
| Sonnet | — | — | — | 0.33 [—]; n=10 | 0.61 [—]; n=5 |
| Luna | — | — | 0.33 [—]; n=10 | — | —; n=5 |
| DeepSeek | — | — | 0.61 [—]; n=5 | —; n=5 | — |

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 0 not applicable; Luna: 0 partial, 0 not applicable; DeepSeek: 0 partial, 0 not applicable.

## Tau Ceti

Full-pass reference: **10 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sol | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sonnet | 10 | 1/1 | 10/10 | 8 | 8 | 80.0% [49.0%, 94.3%] | $1.06 / $1.06 |
| Luna | 10 | 1/1 | 10/10 | 3 | 3 | 30.0% [10.8%, 60.3%] | $0.03 / $0.03 |
| DeepSeek | 10 | 0/1 | 5/10 | 3 | 3 | 60.0% [23.1%, 88.2%] | $0.14 / $0.27 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | — | — | — | — |
| Sol | — | — | — | — | — |
| Sonnet | — | — | — | 0.33 [—]; n=10 | 0.61 [—]; n=5 |
| Luna | — | — | 0.33 [—]; n=10 | — | 0.41 [—]; n=5 |
| DeepSeek | — | — | 0.61 [—]; n=5 | 0.41 [—]; n=5 | — |

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 0 not applicable; Luna: 0 partial, 0 not applicable; DeepSeek: 0 partial, 0 not applicable.

## Lean Pool

Full-pass reference: **10 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sol | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sonnet | 10 | 1/1 | 10/10 | 9 | 9 | 90.0% [59.6%, 98.2%] | $1.54 / $1.54 |
| Luna | 10 | 1/1 | 10/10 | 6 | 6 | 60.0% [31.3%, 83.2%] | $0.05 / $0.05 |
| DeepSeek | 10 | 0/1 | 5/10 | 4 | 4 | 80.0% [37.6%, 96.4%] | $0.17 / $0.35 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | — | — | — | — |
| Sol | — | — | — | — | — |
| Sonnet | — | — | — | 0.41 [—]; n=10 | 1.00 [—]; n=5 |
| Luna | — | — | 0.41 [—]; n=10 | — | 0.41 [—]; n=5 |
| DeepSeek | — | — | 1.00 [—]; n=5 | 0.41 [—]; n=5 | — |

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 0 not applicable; Luna: 0 partial, 0 not applicable; DeepSeek: 0 partial, 0 not applicable.

## OpenAI Math

Full-pass reference: **100 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 100 | 1/1 | 100/100 | 84 | 84 | 84.0% [75.6%, 89.9%] | $34.58 / $34.58 |
| Sol | 100 | 1/1 | 100/100 | 82 | 82 | 82.0% [73.3%, 88.3%] | $12.68 / $12.68 |
| Sonnet | 100 | 1/1 | 100/100 | 78 | 78 | 78.0% [68.9%, 85.0%] | $15.00 / $15.00 |
| Luna | 100 | 1/1 | 100/100 | 25 | 25 | 25.0% [17.5%, 34.3%] | $0.38 / $0.38 |
| DeepSeek | 10 | 0/1 | 5/10 | 4 | 4 | 80.0% [37.6%, 96.4%] | $0.11 / $2.15 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | 0.65 [0.42, 0.82]; n=100 | 0.49 [0.27, 0.70]; n=100 | 0.19 [0.04, 0.29]; n=100 | —; n=5 |
| Sol | 0.65 [0.42, 0.82]; n=100 | — | 0.38 [0.15, 0.59]; n=100 | 0.03 [-0.18, 0.21]; n=100 | 0.61 [—]; n=5 |
| Sonnet | 0.49 [0.27, 0.70]; n=100 | 0.38 [0.15, 0.59]; n=100 | — | 0.08 [-0.11, 0.25]; n=100 | 1.00 [—]; n=5 |
| Luna | 0.19 [0.04, 0.29]; n=100 | 0.03 [-0.18, 0.21]; n=100 | 0.08 [-0.11, 0.25]; n=100 | — | 0.25 [—]; n=5 |
| DeepSeek | —; n=5 | 0.61 [—]; n=5 | 1.00 [—]; n=5 | 0.25 [—]; n=5 | — |

Coverage annotations: Opus: 0 partial, 1 not applicable; Sol: 0 partial, 1 not applicable; Sonnet: 0 partial, 1 not applicable; Luna: 0 partial, 1 not applicable; DeepSeek: 0 partial, 0 not applicable.
