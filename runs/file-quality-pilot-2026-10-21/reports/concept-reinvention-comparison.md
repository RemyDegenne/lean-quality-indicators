# concept-reinvention

Generated 2026-10-21T05:54:53+00:00 · [Methods and notation](../../../AUDIT_METHODS.md) · 2,000 bootstrap draws.

## Library comparison

| Library | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Mathlib | — | — | 2/10<br>20.0% [5.7%, 51.0%] | 0/10<br>0.0% [0.0%, 27.8%] |
| Tau Ceti | — | — | 0/10<br>0.0% [0.0%, 27.8%] | 0/10<br>0.0% [0.0%, 27.8%] |
| Lean Pool | — | — | 4/10<br>40.0% [16.8%, 68.7%] | 0/10<br>0.0% [0.0%, 27.8%] |
| OpenAI Math | 0/1<br>0.0% [0.0%, 79.3%] | 0/1<br>0.0% [0.0%, 79.3%] | 0/2<br>0.0% [0.0%, 65.8%] | 0/2<br>0.0% [0.0%, 65.8%] |

## All libraries

Full-pass reference: **30 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 100 | 0/1 | 1/100 | 0 | 0 | 0.0% [0.0%, 79.3%] | $0.13 / $3.78 |
| Sol | 100 | 0/1 | 1/100 | 0 | 0 | 0.0% [0.0%, 79.3%] | $0.09 / $2.57 |
| Sonnet | 130 | 0/1 | 32/130 | 6 | 6 | 18.8% [8.9%, 35.3%] | $2.29 / $2.15 |
| Luna | 130 | 0/1 | 32/130 | 0 | 0 | 0.0% [0.0%, 10.7%] | $0.16 / $0.15 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Opus | — | —; n=1 | —; n=1 | —; n=1 |
| Sol | —; n=1 | — | —; n=1 | —; n=1 |
| Sonnet | —; n=1 | —; n=1 | — | —; n=32 |
| Luna | —; n=1 | —; n=1 | —; n=32 | — |

Coverage annotations: Opus: 0 partial, 1 not applicable; Sol: 0 partial, 1 not applicable; Sonnet: 0 partial, 6 not applicable; Luna: 0 partial, 0 not applicable.

## Mathlib

Full-pass reference: **10 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sol | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sonnet | 10 | 1/1 | 10/10 | 2 | 2 | 20.0% [5.7%, 51.0%] | $0.71 / $0.71 |
| Luna | 10 | 1/1 | 10/10 | 0 | 0 | 0.0% [0.0%, 27.8%] | $0.05 / $0.05 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Opus | — | — | — | — |
| Sol | — | — | — | — |
| Sonnet | — | — | — | —; n=10 |
| Luna | — | — | —; n=10 | — |

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 1 not applicable; Luna: 0 partial, 0 not applicable.

## Tau Ceti

Full-pass reference: **10 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sol | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sonnet | 10 | 1/1 | 10/10 | 0 | 0 | 0.0% [0.0%, 27.8%] | $0.39 / $0.39 |
| Luna | 10 | 1/1 | 10/10 | 0 | 0 | 0.0% [0.0%, 27.8%] | $0.04 / $0.04 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Opus | — | — | — | — |
| Sol | — | — | — | — |
| Sonnet | — | — | — | —; n=10 |
| Luna | — | — | —; n=10 | — |

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 3 not applicable; Luna: 0 partial, 0 not applicable.

## Lean Pool

Full-pass reference: **10 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sol | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sonnet | 10 | 1/1 | 10/10 | 4 | 4 | 40.0% [16.8%, 68.7%] | $1.10 / $1.10 |
| Luna | 10 | 1/1 | 10/10 | 0 | 0 | 0.0% [0.0%, 27.8%] | $0.06 / $0.06 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Opus | — | — | — | — |
| Sol | — | — | — | — |
| Sonnet | — | — | — | —; n=10 |
| Luna | — | — | —; n=10 | — |

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 1 not applicable; Luna: 0 partial, 0 not applicable.

## OpenAI Math

Full-pass reference: **0 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 100 | 0/1 | 1/100 | 0 | 0 | 0.0% [0.0%, 79.3%] | $0.13 / $0.00 |
| Sol | 100 | 0/1 | 1/100 | 0 | 0 | 0.0% [0.0%, 79.3%] | $0.09 / $0.00 |
| Sonnet | 100 | 0/1 | 2/100 | 0 | 0 | 0.0% [0.0%, 65.8%] | $0.10 / $0.00 |
| Luna | 100 | 0/1 | 2/100 | 0 | 0 | 0.0% [0.0%, 65.8%] | $0.01 / $0.00 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Opus | — | —; n=1 | —; n=1 | —; n=1 |
| Sol | —; n=1 | — | —; n=1 | —; n=1 |
| Sonnet | —; n=1 | —; n=1 | — | —; n=2 |
| Luna | —; n=1 | —; n=1 | —; n=2 | — |

Coverage annotations: Opus: 0 partial, 1 not applicable; Sol: 0 partial, 1 not applicable; Sonnet: 0 partial, 1 not applicable; Luna: 0 partial, 0 not applicable.
