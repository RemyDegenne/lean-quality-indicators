# vacuity-and-misstatement

Generated 2026-10-21T22:56:08+00:00 · [Methods and notation](../../../AUDIT_METHODS.md) · 2,000 bootstrap draws.

## Library comparison

| Library | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Mathlib | — | — | 3/10<br>30.0% [10.8%, 60.3%] | 1/10<br>10.0% [1.8%, 40.4%] | 1/2<br>50.0% [9.5%, 90.5%] |
| Tau Ceti | — | — | 0/10<br>0.0% [0.0%, 27.8%] | 1/10<br>10.0% [1.8%, 40.4%] | 1/2<br>50.0% [9.5%, 90.5%] |
| Lean Pool | — | — | 2/10<br>20.0% [5.7%, 51.0%] | 0/10<br>0.0% [0.0%, 27.8%] | 1/2<br>50.0% [9.5%, 90.5%] |
| OpenAI Math | 0/100<br>0.0% [0.0%, 3.7%] | 0/100<br>0.0% [0.0%, 3.7%] | 3/100<br>3.0% [1.0%, 8.5%] | 3/100<br>3.0% [1.0%, 8.5%] | 0/2<br>0.0% [0.0%, 65.8%] |

## All libraries

Full-pass reference: **130 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 100 | 1/1 | 100/100 | 0 | 0 | 0.0% [0.0%, 3.7%] | $21.38 / $27.79 |
| Sol | 100 | 1/1 | 100/100 | 0 | 0 | 0.0% [0.0%, 3.7%] | $9.89 / $12.85 |
| Sonnet | 130 | 1/1 | 130/130 | 8 | 8 | 6.2% [3.2%, 11.7%] | $12.33 / $12.33 |
| Luna | 130 | 1/1 | 130/130 | 5 | 5 | 3.8% [1.7%, 8.7%] | $0.58 / $0.58 |
| DeepSeek | 40 | 0/1 | 8/40 | 3 | 3 | 37.5% [13.7%, 69.4%] | $0.27 / $4.32 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | —; n=100 | —; n=100 | —; n=100 | —; n=2 |
| Sol | —; n=100 | — | —; n=100 | —; n=100 | —; n=2 |
| Sonnet | —; n=100 | —; n=100 | — | 0.12 [-0.06, 0.41]; n=130 | 0.75 [—]; n=8 |
| Luna | —; n=100 | —; n=100 | 0.12 [-0.06, 0.41]; n=130 | — | —; n=8 |
| DeepSeek | —; n=2 | —; n=2 | 0.75 [—]; n=8 | —; n=8 | — |

Coverage annotations: Opus: 0 partial, 1 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 0 not applicable; Luna: 0 partial, 0 not applicable; DeepSeek: 0 partial, 0 not applicable.

## Mathlib

Full-pass reference: **10 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sol | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sonnet | 10 | 1/1 | 10/10 | 3 | 3 | 30.0% [10.8%, 60.3%] | $0.48 / $0.48 |
| Luna | 10 | 1/1 | 10/10 | 1 | 1 | 10.0% [1.8%, 40.4%] | $0.04 / $0.04 |
| DeepSeek | 10 | 0/1 | 2/10 | 1 | 1 | 50.0% [9.5%, 90.5%] | $0.04 / $0.22 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | — | — | — | — |
| Sol | — | — | — | — | — |
| Sonnet | — | — | — | -0.22 [—]; n=10 | 1.00 [—]; n=2 |
| Luna | — | — | -0.22 [—]; n=10 | — | —; n=2 |
| DeepSeek | — | — | 1.00 [—]; n=2 | —; n=2 | — |

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 0 not applicable; Luna: 0 partial, 0 not applicable; DeepSeek: 0 partial, 0 not applicable.

## Tau Ceti

Full-pass reference: **10 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sol | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sonnet | 10 | 1/1 | 10/10 | 0 | 0 | 0.0% [0.0%, 27.8%] | $0.62 / $0.62 |
| Luna | 10 | 1/1 | 10/10 | 1 | 1 | 10.0% [1.8%, 40.4%] | $0.05 / $0.05 |
| DeepSeek | 10 | 0/1 | 2/10 | 1 | 1 | 50.0% [9.5%, 90.5%] | $0.07 / $0.35 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | — | — | — | — |
| Sol | — | — | — | — | — |
| Sonnet | — | — | — | —; n=10 | —; n=2 |
| Luna | — | — | —; n=10 | — | —; n=2 |
| DeepSeek | — | — | —; n=2 | —; n=2 | — |

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 0 not applicable; Luna: 0 partial, 0 not applicable; DeepSeek: 0 partial, 0 not applicable.

## Lean Pool

Full-pass reference: **10 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sol | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sonnet | 10 | 1/1 | 10/10 | 2 | 2 | 20.0% [5.7%, 51.0%] | $1.14 / $1.14 |
| Luna | 10 | 1/1 | 10/10 | 0 | 0 | 0.0% [0.0%, 27.8%] | $0.05 / $0.05 |
| DeepSeek | 10 | 0/1 | 2/10 | 1 | 1 | 50.0% [9.5%, 90.5%] | $0.05 / $0.24 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | — | — | — | — |
| Sol | — | — | — | — | — |
| Sonnet | — | — | — | —; n=10 | 1.00 [—]; n=2 |
| Luna | — | — | —; n=10 | — | —; n=2 |
| DeepSeek | — | — | 1.00 [—]; n=2 | —; n=2 | — |

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 0 not applicable; Luna: 0 partial, 0 not applicable; DeepSeek: 0 partial, 0 not applicable.

## OpenAI Math

Full-pass reference: **100 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 100 | 1/1 | 100/100 | 0 | 0 | 0.0% [0.0%, 3.7%] | $21.38 / $21.38 |
| Sol | 100 | 1/1 | 100/100 | 0 | 0 | 0.0% [0.0%, 3.7%] | $9.89 / $9.89 |
| Sonnet | 100 | 1/1 | 100/100 | 3 | 3 | 3.0% [1.0%, 8.5%] | $10.09 / $10.09 |
| Luna | 100 | 1/1 | 100/100 | 3 | 3 | 3.0% [1.0%, 8.5%] | $0.45 / $0.45 |
| DeepSeek | 10 | 0/1 | 2/10 | 0 | 0 | 0.0% [0.0%, 65.8%] | $0.10 / $5.15 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | —; n=100 | —; n=100 | —; n=100 | —; n=2 |
| Sol | —; n=100 | — | —; n=100 | —; n=100 | —; n=2 |
| Sonnet | —; n=100 | —; n=100 | — | 0.31 [—]; n=100 | —; n=2 |
| Luna | —; n=100 | —; n=100 | 0.31 [—]; n=100 | — | —; n=2 |
| DeepSeek | —; n=2 | —; n=2 | —; n=2 | —; n=2 | — |

Coverage annotations: Opus: 0 partial, 1 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 0 not applicable; Luna: 0 partial, 0 not applicable; DeepSeek: 0 partial, 0 not applicable.
