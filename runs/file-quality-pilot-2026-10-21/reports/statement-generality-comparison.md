# statement-generality

Generated 2026-10-22T00:29:25+00:00 · [Methods and notation](../../../AUDIT_METHODS.md) · 2,000 bootstrap draws.

## Library comparison

| Library | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Mathlib | — | — | 6/10<br>60.0% [31.3%, 83.2%] | 2/10<br>20.0% [5.7%, 51.0%] | 6/7<br>85.7% [48.7%, 97.4%] |
| Tau Ceti | — | — | 3/10<br>30.0% [10.8%, 60.3%] | 1/10<br>10.0% [1.8%, 40.4%] | 4/7<br>57.1% [25.0%, 84.2%] |
| Lean Pool | — | — | 9/10<br>90.0% [59.6%, 98.2%] | 8/10<br>80.0% [49.0%, 94.3%] | 7/7<br>100.0% [64.6%, 100.0%] |
| OpenAI Math | 67/100<br>67.0% [57.3%, 75.4%] | 79/100<br>79.0% [70.0%, 85.8%] | 60/100<br>60.0% [50.2%, 69.1%] | 47/100<br>47.0% [37.5%, 56.7%] | 7/7<br>100.0% [64.6%, 100.0%] |

## All libraries

Full-pass reference: **130 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 100 | 1/1 | 100/100 | 67 | 67 | 67.0% [57.3%, 75.4%] | $32.26 / $41.93 |
| Sol | 100 | 1/1 | 100/100 | 79 | 79 | 79.0% [70.0%, 85.8%] | $13.16 / $17.11 |
| Sonnet | 130 | 1/1 | 130/130 | 78 | 78 | 60.0% [51.4%, 68.0%] | $16.38 / $16.38 |
| Luna | 130 | 1/1 | 130/130 | 58 | 58 | 44.6% [36.3%, 53.2%] | $0.63 / $0.63 |
| DeepSeek | 40 | 0/1 | 28/40 | 24 | 24 | 85.7% [68.5%, 94.3%] | $0.78 / $3.60 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | 0.47 [0.28, 0.66]; n=100 | 0.51 [0.33, 0.67]; n=100 | 0.36 [0.18, 0.53]; n=100 | —; n=7 |
| Sol | 0.47 [0.28, 0.66]; n=100 | — | 0.48 [0.30, 0.63]; n=100 | 0.39 [0.22, 0.53]; n=100 | —; n=7 |
| Sonnet | 0.51 [0.33, 0.67]; n=100 | 0.48 [0.30, 0.63]; n=100 | — | 0.48 [0.34, 0.61]; n=130 | 0.59 [0.33, 0.85]; n=28 |
| Luna | 0.36 [0.18, 0.53]; n=100 | 0.39 [0.22, 0.53]; n=100 | 0.48 [0.34, 0.61]; n=130 | — | 0.33 [0.16, 0.52]; n=28 |
| DeepSeek | —; n=7 | —; n=7 | 0.59 [0.33, 0.85]; n=28 | 0.33 [0.16, 0.52]; n=28 | — |

Coverage annotations: Opus: 0 partial, 1 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 1 not applicable; Luna: 0 partial, 0 not applicable; DeepSeek: 0 partial, 0 not applicable.

## Mathlib

Full-pass reference: **10 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sol | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sonnet | 10 | 1/1 | 10/10 | 6 | 6 | 60.0% [31.3%, 83.2%] | $1.04 / $1.04 |
| Luna | 10 | 1/1 | 10/10 | 2 | 2 | 20.0% [5.7%, 51.0%] | $0.05 / $0.05 |
| DeepSeek | 10 | 0/1 | 7/10 | 6 | 6 | 85.7% [48.7%, 97.4%] | $0.23 / $0.33 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | — | — | — | — |
| Sol | — | — | — | — | — |
| Sonnet | — | — | — | -0.10 [—]; n=10 | 0.65 [—]; n=7 |
| Luna | — | — | -0.10 [—]; n=10 | — | 0.17 [—]; n=7 |
| DeepSeek | — | — | 0.65 [—]; n=7 | 0.17 [—]; n=7 | — |

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 0 not applicable; Luna: 0 partial, 0 not applicable; DeepSeek: 0 partial, 0 not applicable.

## Tau Ceti

Full-pass reference: **10 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sol | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sonnet | 10 | 1/1 | 10/10 | 3 | 3 | 30.0% [10.8%, 60.3%] | $0.66 / $0.66 |
| Luna | 10 | 1/1 | 10/10 | 1 | 1 | 10.0% [1.8%, 40.4%] | $0.04 / $0.04 |
| DeepSeek | 10 | 0/1 | 7/10 | 4 | 4 | 57.1% [25.0%, 84.2%] | $0.20 / $0.28 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | — | — | — | — |
| Sol | — | — | — | — | — |
| Sonnet | — | — | — | -0.22 [—]; n=10 | 0.55 [—]; n=7 |
| Luna | — | — | -0.22 [—]; n=10 | — | —; n=7 |
| DeepSeek | — | — | 0.55 [—]; n=7 | —; n=7 | — |

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 0 not applicable; Luna: 0 partial, 0 not applicable; DeepSeek: 0 partial, 0 not applicable.

## Lean Pool

Full-pass reference: **10 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sol | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sonnet | 10 | 1/1 | 10/10 | 9 | 9 | 90.0% [59.6%, 98.2%] | $1.37 / $1.37 |
| Luna | 10 | 1/1 | 10/10 | 8 | 8 | 80.0% [49.0%, 94.3%] | $0.06 / $0.06 |
| DeepSeek | 10 | 0/1 | 7/10 | 7 | 7 | 100.0% [64.6%, 100.0%] | $0.13 / $0.18 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | — | — | — | — |
| Sol | — | — | — | — | — |
| Sonnet | — | — | — | 0.67 [—]; n=10 | —; n=7 |
| Luna | — | — | 0.67 [—]; n=10 | — | —; n=7 |
| DeepSeek | — | — | —; n=7 | —; n=7 | — |

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 0 not applicable; Luna: 0 partial, 0 not applicable; DeepSeek: 0 partial, 0 not applicable.

## OpenAI Math

Full-pass reference: **100 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 100 | 1/1 | 100/100 | 67 | 67 | 67.0% [57.3%, 75.4%] | $32.26 / $32.26 |
| Sol | 100 | 1/1 | 100/100 | 79 | 79 | 79.0% [70.0%, 85.8%] | $13.16 / $13.16 |
| Sonnet | 100 | 1/1 | 100/100 | 60 | 60 | 60.0% [50.2%, 69.1%] | $13.31 / $13.31 |
| Luna | 100 | 1/1 | 100/100 | 47 | 47 | 47.0% [37.5%, 56.7%] | $0.48 / $0.48 |
| DeepSeek | 10 | 0/1 | 7/10 | 7 | 7 | 100.0% [64.6%, 100.0%] | $0.22 / $3.13 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | 0.47 [0.28, 0.65]; n=100 | 0.51 [0.33, 0.68]; n=100 | 0.36 [0.18, 0.53]; n=100 | —; n=7 |
| Sol | 0.47 [0.28, 0.65]; n=100 | — | 0.48 [0.31, 0.64]; n=100 | 0.39 [0.23, 0.53]; n=100 | —; n=7 |
| Sonnet | 0.51 [0.33, 0.68]; n=100 | 0.48 [0.31, 0.64]; n=100 | — | 0.52 [0.36, 0.68]; n=100 | —; n=7 |
| Luna | 0.36 [0.18, 0.53]; n=100 | 0.39 [0.23, 0.53]; n=100 | 0.52 [0.36, 0.68]; n=100 | — | —; n=7 |
| DeepSeek | —; n=7 | —; n=7 | —; n=7 | —; n=7 | — |

Coverage annotations: Opus: 0 partial, 1 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 1 not applicable; Luna: 0 partial, 0 not applicable; DeepSeek: 0 partial, 0 not applicable.
