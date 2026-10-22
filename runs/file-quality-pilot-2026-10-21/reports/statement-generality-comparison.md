# statement-generality

Generated 2026-10-22T00:03:28+00:00 · [Methods and notation](../../../AUDIT_METHODS.md) · 2,000 bootstrap draws.

## Library comparison

| Library | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Mathlib | — | — | 6/10<br>60.0% [31.3%, 83.2%] | 2/10<br>20.0% [5.7%, 51.0%] | 4/5<br>80.0% [37.6%, 96.4%] |
| Tau Ceti | — | — | 3/10<br>30.0% [10.8%, 60.3%] | 1/10<br>10.0% [1.8%, 40.4%] | 3/6<br>50.0% [18.8%, 81.2%] |
| Lean Pool | — | — | 9/10<br>90.0% [59.6%, 98.2%] | 8/10<br>80.0% [49.0%, 94.3%] | 6/6<br>100.0% [61.0%, 100.0%] |
| OpenAI Math | 67/100<br>67.0% [57.3%, 75.4%] | 79/100<br>79.0% [70.0%, 85.8%] | 60/100<br>60.0% [50.2%, 69.1%] | 47/100<br>47.0% [37.5%, 56.7%] | 6/6<br>100.0% [61.0%, 100.0%] |

## All libraries

Full-pass reference: **130 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 100 | 1/1 | 100/100 | 67 | 67 | 67.0% [57.3%, 75.4%] | $32.26 / $41.93 |
| Sol | 100 | 1/1 | 100/100 | 79 | 79 | 79.0% [70.0%, 85.8%] | $13.16 / $17.11 |
| Sonnet | 130 | 1/1 | 130/130 | 78 | 78 | 60.0% [51.4%, 68.0%] | $16.38 / $16.38 |
| Luna | 130 | 1/1 | 130/130 | 58 | 58 | 44.6% [36.3%, 53.2%] | $0.63 / $0.63 |
| DeepSeek | 40 | 0/1 | 23/40 | 19 | 19 | 82.6% [62.9%, 93.0%] | $0.65 / $3.67 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | 0.47 [0.28, 0.66]; n=100 | 0.51 [0.33, 0.67]; n=100 | 0.36 [0.18, 0.53]; n=100 | —; n=6 |
| Sol | 0.47 [0.28, 0.66]; n=100 | — | 0.48 [0.30, 0.63]; n=100 | 0.39 [0.22, 0.53]; n=100 | —; n=6 |
| Sonnet | 0.51 [0.33, 0.67]; n=100 | 0.48 [0.30, 0.63]; n=100 | — | 0.48 [0.34, 0.61]; n=130 | 0.63 [0.35, 0.90]; n=23 |
| Luna | 0.36 [0.18, 0.53]; n=100 | 0.39 [0.22, 0.53]; n=100 | 0.48 [0.34, 0.61]; n=130 | — | 0.37 [0.17, 0.58]; n=23 |
| DeepSeek | —; n=6 | —; n=6 | 0.63 [0.35, 0.90]; n=23 | 0.37 [0.17, 0.58]; n=23 | — |

Coverage annotations: Opus: 0 partial, 1 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 1 not applicable; Luna: 0 partial, 0 not applicable; DeepSeek: 0 partial, 0 not applicable.

## Mathlib

Full-pass reference: **10 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sol | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sonnet | 10 | 1/1 | 10/10 | 6 | 6 | 60.0% [31.3%, 83.2%] | $1.04 / $1.04 |
| Luna | 10 | 1/1 | 10/10 | 2 | 2 | 20.0% [5.7%, 51.0%] | $0.05 / $0.05 |
| DeepSeek | 10 | 0/1 | 5/10 | 4 | 4 | 80.0% [37.6%, 96.4%] | $0.17 / $0.35 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | — | — | — | — |
| Sol | — | — | — | — | — |
| Sonnet | — | — | — | -0.10 [—]; n=10 | 0.61 [—]; n=5 |
| Luna | — | — | -0.10 [—]; n=10 | — | 0.25 [—]; n=5 |
| DeepSeek | — | — | 0.61 [—]; n=5 | 0.25 [—]; n=5 | — |

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 0 not applicable; Luna: 0 partial, 0 not applicable; DeepSeek: 0 partial, 0 not applicable.

## Tau Ceti

Full-pass reference: **10 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sol | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sonnet | 10 | 1/1 | 10/10 | 3 | 3 | 30.0% [10.8%, 60.3%] | $0.66 / $0.66 |
| Luna | 10 | 1/1 | 10/10 | 1 | 1 | 10.0% [1.8%, 40.4%] | $0.04 / $0.04 |
| DeepSeek | 10 | 0/1 | 6/10 | 3 | 3 | 50.0% [18.8%, 81.2%] | $0.19 / $0.31 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | — | — | — | — |
| Sol | — | — | — | — | — |
| Sonnet | — | — | — | -0.22 [—]; n=10 | 0.71 [—]; n=6 |
| Luna | — | — | -0.22 [—]; n=10 | — | —; n=6 |
| DeepSeek | — | — | 0.71 [—]; n=6 | —; n=6 | — |

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 0 not applicable; Luna: 0 partial, 0 not applicable; DeepSeek: 0 partial, 0 not applicable.

## Lean Pool

Full-pass reference: **10 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sol | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sonnet | 10 | 1/1 | 10/10 | 9 | 9 | 90.0% [59.6%, 98.2%] | $1.37 / $1.37 |
| Luna | 10 | 1/1 | 10/10 | 8 | 8 | 80.0% [49.0%, 94.3%] | $0.06 / $0.06 |
| DeepSeek | 10 | 0/1 | 6/10 | 6 | 6 | 100.0% [61.0%, 100.0%] | $0.11 / $0.18 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | — | — | — | — |
| Sol | — | — | — | — | — |
| Sonnet | — | — | — | 0.67 [—]; n=10 | —; n=6 |
| Luna | — | — | 0.67 [—]; n=10 | — | —; n=6 |
| DeepSeek | — | — | —; n=6 | —; n=6 | — |

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 0 not applicable; Luna: 0 partial, 0 not applicable; DeepSeek: 0 partial, 0 not applicable.

## OpenAI Math

Full-pass reference: **100 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 100 | 1/1 | 100/100 | 67 | 67 | 67.0% [57.3%, 75.4%] | $32.26 / $32.26 |
| Sol | 100 | 1/1 | 100/100 | 79 | 79 | 79.0% [70.0%, 85.8%] | $13.16 / $13.16 |
| Sonnet | 100 | 1/1 | 100/100 | 60 | 60 | 60.0% [50.2%, 69.1%] | $13.31 / $13.31 |
| Luna | 100 | 1/1 | 100/100 | 47 | 47 | 47.0% [37.5%, 56.7%] | $0.48 / $0.48 |
| DeepSeek | 10 | 0/1 | 6/10 | 6 | 6 | 100.0% [61.0%, 100.0%] | $0.18 / $2.97 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | 0.47 [0.28, 0.65]; n=100 | 0.51 [0.33, 0.68]; n=100 | 0.36 [0.18, 0.53]; n=100 | —; n=6 |
| Sol | 0.47 [0.28, 0.65]; n=100 | — | 0.48 [0.31, 0.64]; n=100 | 0.39 [0.23, 0.53]; n=100 | —; n=6 |
| Sonnet | 0.51 [0.33, 0.68]; n=100 | 0.48 [0.31, 0.64]; n=100 | — | 0.52 [0.36, 0.68]; n=100 | —; n=6 |
| Luna | 0.36 [0.18, 0.53]; n=100 | 0.39 [0.23, 0.53]; n=100 | 0.52 [0.36, 0.68]; n=100 | — | —; n=6 |
| DeepSeek | —; n=6 | —; n=6 | —; n=6 | —; n=6 | — |

Coverage annotations: Opus: 0 partial, 1 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 1 not applicable; Luna: 0 partial, 0 not applicable; DeepSeek: 0 partial, 0 not applicable.
