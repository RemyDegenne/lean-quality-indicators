# statement-generality

Generated 2026-10-21T05:54:53+00:00 · [Methods and notation](../../../AUDIT_METHODS.md) · 2,000 bootstrap draws.

## Library comparison

| Library | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Mathlib | — | — | 6/10<br>60.0% [31.3%, 83.2%] | 2/10<br>20.0% [5.7%, 51.0%] |
| Tau Ceti | — | — | 3/10<br>30.0% [10.8%, 60.3%] | 1/10<br>10.0% [1.8%, 40.4%] |
| Lean Pool | — | — | 9/10<br>90.0% [59.6%, 98.2%] | 8/10<br>80.0% [49.0%, 94.3%] |
| OpenAI Math | 1/1<br>100.0% [20.7%, 100.0%] | 1/1<br>100.0% [20.7%, 100.0%] | 2/2<br>100.0% [34.2%, 100.0%] | 2/2<br>100.0% [34.2%, 100.0%] |

## All libraries

Full-pass reference: **30 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 100 | 0/1 | 1/100 | 1 | 1 | 100.0% [20.7%, 100.0%] | $0.96 / $28.66 |
| Sol | 100 | 0/1 | 1/100 | 1 | 1 | 100.0% [20.7%, 100.0%] | $0.14 / $4.06 |
| Sonnet | 130 | 0/1 | 32/130 | 20 | 20 | 62.5% [45.3%, 77.1%] | $3.34 / $3.13 |
| Luna | 130 | 0/1 | 32/130 | 13 | 13 | 40.6% [25.5%, 57.7%] | $0.16 / $0.15 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Opus | — | —; n=1 | —; n=1 | —; n=1 |
| Sol | —; n=1 | — | —; n=1 | —; n=1 |
| Sonnet | —; n=1 | —; n=1 | — | 0.38 [0.09, 0.64]; n=32 |
| Luna | —; n=1 | —; n=1 | 0.38 [0.09, 0.64]; n=32 | — |

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 0 not applicable; Luna: 0 partial, 0 not applicable.

## Mathlib

Full-pass reference: **10 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sol | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sonnet | 10 | 1/1 | 10/10 | 6 | 6 | 60.0% [31.3%, 83.2%] | $1.04 / $1.04 |
| Luna | 10 | 1/1 | 10/10 | 2 | 2 | 20.0% [5.7%, 51.0%] | $0.05 / $0.05 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Opus | — | — | — | — |
| Sol | — | — | — | — |
| Sonnet | — | — | — | -0.10 [—]; n=10 |
| Luna | — | — | -0.10 [—]; n=10 | — |

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 0 not applicable; Luna: 0 partial, 0 not applicable.

## Tau Ceti

Full-pass reference: **10 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sol | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sonnet | 10 | 1/1 | 10/10 | 3 | 3 | 30.0% [10.8%, 60.3%] | $0.66 / $0.66 |
| Luna | 10 | 1/1 | 10/10 | 1 | 1 | 10.0% [1.8%, 40.4%] | $0.04 / $0.04 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Opus | — | — | — | — |
| Sol | — | — | — | — |
| Sonnet | — | — | — | -0.22 [—]; n=10 |
| Luna | — | — | -0.22 [—]; n=10 | — |

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 0 not applicable; Luna: 0 partial, 0 not applicable.

## Lean Pool

Full-pass reference: **10 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sol | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sonnet | 10 | 1/1 | 10/10 | 9 | 9 | 90.0% [59.6%, 98.2%] | $1.37 / $1.37 |
| Luna | 10 | 1/1 | 10/10 | 8 | 8 | 80.0% [49.0%, 94.3%] | $0.06 / $0.06 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Opus | — | — | — | — |
| Sol | — | — | — | — |
| Sonnet | — | — | — | 0.67 [—]; n=10 |
| Luna | — | — | 0.67 [—]; n=10 | — |

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 0 not applicable; Luna: 0 partial, 0 not applicable.

## OpenAI Math

Full-pass reference: **0 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 100 | 0/1 | 1/100 | 1 | 1 | 100.0% [20.7%, 100.0%] | $0.96 / $0.00 |
| Sol | 100 | 0/1 | 1/100 | 1 | 1 | 100.0% [20.7%, 100.0%] | $0.14 / $0.00 |
| Sonnet | 100 | 0/1 | 2/100 | 2 | 2 | 100.0% [34.2%, 100.0%] | $0.27 / $0.00 |
| Luna | 100 | 0/1 | 2/100 | 2 | 2 | 100.0% [34.2%, 100.0%] | $0.01 / $0.00 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Opus | — | —; n=1 | —; n=1 | —; n=1 |
| Sol | —; n=1 | — | —; n=1 | —; n=1 |
| Sonnet | —; n=1 | —; n=1 | — | —; n=2 |
| Luna | —; n=1 | —; n=1 | —; n=2 | — |

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 0 not applicable; Luna: 0 partial, 0 not applicable.
