# simp-interface

Generated 2026-10-21T05:54:53+00:00 · [Methods and notation](../../../AUDIT_METHODS.md) · 2,000 bootstrap draws.

## Library comparison

| Library | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Mathlib | — | — | 4/10<br>40.0% [16.8%, 68.7%] | 4/10<br>40.0% [16.8%, 68.7%] |
| Tau Ceti | — | — | 3/10<br>30.0% [10.8%, 60.3%] | 1/10<br>10.0% [1.8%, 40.4%] |
| Lean Pool | — | — | 6/10<br>60.0% [31.3%, 83.2%] | 6/10<br>60.0% [31.3%, 83.2%] |
| OpenAI Math | 1/1<br>100.0% [20.7%, 100.0%] | 0/1<br>0.0% [0.0%, 79.3%] | 1/2<br>50.0% [9.5%, 90.5%] | 1/1<br>100.0% [20.7%, 100.0%] |

## All libraries

Full-pass reference: **30 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 100 | 0/1 | 1/100 | 1 | 1 | 100.0% [20.7%, 100.0%] | $0.22 / $6.59 |
| Sol | 100 | 0/1 | 1/100 | 0 | 0 | 0.0% [0.0%, 79.3%] | $0.09 / $2.67 |
| Sonnet | 130 | 0/1 | 32/130 | 14 | 14 | 43.8% [28.2%, 60.7%] | $2.56 / $2.40 |
| Luna | 130 | 0/1 | 31/130 | 12 | 12 | 38.7% [23.7%, 56.2%] | $0.16 / $0.15 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Opus | — | —; n=1 | —; n=1 | —; n=1 |
| Sol | —; n=1 | — | —; n=1 | —; n=1 |
| Sonnet | —; n=1 | —; n=1 | — | 0.40 [0.09, 0.68]; n=31 |
| Luna | —; n=1 | —; n=1 | 0.40 [0.09, 0.68]; n=31 | — |

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 1 not applicable; Luna: 0 partial, 0 not applicable.

## Mathlib

Full-pass reference: **10 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sol | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sonnet | 10 | 1/1 | 10/10 | 4 | 4 | 40.0% [16.8%, 68.7%] | $0.68 / $0.68 |
| Luna | 10 | 1/1 | 10/10 | 4 | 4 | 40.0% [16.8%, 68.7%] | $0.05 / $0.05 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Opus | — | — | — | — |
| Sol | — | — | — | — |
| Sonnet | — | — | — | 0.58 [0.00, 1.00]; n=10 |
| Luna | — | — | 0.58 [0.00, 1.00]; n=10 | — |

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 1 not applicable; Luna: 0 partial, 0 not applicable.

## Tau Ceti

Full-pass reference: **10 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sol | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sonnet | 10 | 1/1 | 10/10 | 3 | 3 | 30.0% [10.8%, 60.3%] | $0.68 / $0.68 |
| Luna | 10 | 1/1 | 10/10 | 1 | 1 | 10.0% [1.8%, 40.4%] | $0.05 / $0.05 |

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
| Sonnet | 10 | 1/1 | 10/10 | 6 | 6 | 60.0% [31.3%, 83.2%] | $1.04 / $1.04 |
| Luna | 10 | 1/1 | 10/10 | 6 | 6 | 60.0% [31.3%, 83.2%] | $0.06 / $0.06 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Opus | — | — | — | — |
| Sol | — | — | — | — |
| Sonnet | — | — | — | 0.58 [-0.17, 1.00]; n=10 |
| Luna | — | — | 0.58 [-0.17, 1.00]; n=10 | — |

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 0 not applicable; Luna: 0 partial, 0 not applicable.

## OpenAI Math

Full-pass reference: **0 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 100 | 0/1 | 1/100 | 1 | 1 | 100.0% [20.7%, 100.0%] | $0.22 / $0.00 |
| Sol | 100 | 0/1 | 1/100 | 0 | 0 | 0.0% [0.0%, 79.3%] | $0.09 / $0.00 |
| Sonnet | 100 | 0/1 | 2/100 | 1 | 1 | 50.0% [9.5%, 90.5%] | $0.18 / $0.00 |
| Luna | 100 | 0/1 | 1/100 | 1 | 1 | 100.0% [20.7%, 100.0%] | $0.01 / $0.00 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Opus | — | —; n=1 | —; n=1 | —; n=1 |
| Sol | —; n=1 | — | —; n=1 | —; n=1 |
| Sonnet | —; n=1 | —; n=1 | — | —; n=1 |
| Luna | —; n=1 | —; n=1 | —; n=1 | — |

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 0 not applicable; Luna: 0 partial, 0 not applicable.
