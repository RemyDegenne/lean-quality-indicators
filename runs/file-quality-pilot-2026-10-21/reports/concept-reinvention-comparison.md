# concept-reinvention

Generated 2026-10-22T00:29:25+00:00 · [Methods and notation](../../../AUDIT_METHODS.md) · 2,000 bootstrap draws.

## Library comparison

| Library | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Mathlib | — | — | 2/10<br>20.0% [5.7%, 51.0%] | 0/10<br>0.0% [0.0%, 27.8%] | 2/7<br>28.6% [8.2%, 64.1%] |
| Tau Ceti | — | — | 0/10<br>0.0% [0.0%, 27.8%] | 0/10<br>0.0% [0.0%, 27.8%] | 0/7<br>0.0% [0.0%, 35.4%] |
| Lean Pool | — | — | 4/10<br>40.0% [16.8%, 68.7%] | 0/10<br>0.0% [0.0%, 27.8%] | 3/7<br>42.9% [15.8%, 75.0%] |
| OpenAI Math | 7/100<br>7.0% [3.4%, 13.7%] | 1/100<br>1.0% [0.2%, 5.4%] | 6/100<br>6.0% [2.8%, 12.5%] | 5/100<br>5.0% [2.2%, 11.2%] | 1/7<br>14.3% [2.6%, 51.3%] |

## All libraries

Full-pass reference: **130 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 100 | 1/1 | 100/100 | 7 | 7 | 7.0% [3.4%, 13.7%] | $15.66 / $20.36 |
| Sol | 100 | 1/1 | 100/100 | 1 | 1 | 1.0% [0.2%, 5.4%] | $8.47 / $11.02 |
| Sonnet | 130 | 1/1 | 130/130 | 12 | 12 | 9.2% [5.4%, 15.4%] | $8.99 / $8.99 |
| Luna | 130 | 1/1 | 130/130 | 5 | 5 | 3.8% [1.7%, 8.7%] | $0.65 / $0.65 |
| DeepSeek | 40 | 0/1 | 28/40 | 6 | 6 | 21.4% [10.2%, 39.5%] | $0.45 / $2.07 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | 0.37 [—]; n=100 | 0.59 [0.22, 0.88]; n=100 | 0.12 [-0.08, 0.45]; n=100 | 1.00 [—]; n=7 |
| Sol | 0.37 [—]; n=100 | — | 0.40 [—]; n=100 | 0.44 [—]; n=100 | 1.00 [—]; n=7 |
| Sonnet | 0.59 [0.22, 0.88]; n=100 | 0.40 [—]; n=100 | — | 0.07 [-0.08, 0.33]; n=130 | 0.53 [-0.04, 0.88]; n=28 |
| Luna | 0.12 [-0.08, 0.45]; n=100 | 0.44 [—]; n=100 | 0.07 [-0.08, 0.33]; n=130 | — | 0.37 [—]; n=28 |
| DeepSeek | 1.00 [—]; n=7 | 1.00 [—]; n=7 | 0.53 [-0.04, 0.88]; n=28 | 0.37 [—]; n=28 | — |

Coverage annotations: Opus: 0 partial, 49 not applicable; Sol: 0 partial, 22 not applicable; Sonnet: 0 partial, 44 not applicable; Luna: 0 partial, 1 not applicable; DeepSeek: 0 partial, 2 not applicable.

## Mathlib

Full-pass reference: **10 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sol | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sonnet | 10 | 1/1 | 10/10 | 2 | 2 | 20.0% [5.7%, 51.0%] | $0.71 / $0.71 |
| Luna | 10 | 1/1 | 10/10 | 0 | 0 | 0.0% [0.0%, 27.8%] | $0.05 / $0.05 |
| DeepSeek | 10 | 0/1 | 7/10 | 2 | 2 | 28.6% [8.2%, 64.1%] | $0.19 / $0.27 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | — | — | — | — |
| Sol | — | — | — | — | — |
| Sonnet | — | — | — | —; n=10 | 0.65 [—]; n=7 |
| Luna | — | — | —; n=10 | — | —; n=7 |
| DeepSeek | — | — | 0.65 [—]; n=7 | —; n=7 | — |

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 1 not applicable; Luna: 0 partial, 0 not applicable; DeepSeek: 0 partial, 0 not applicable.

## Tau Ceti

Full-pass reference: **10 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sol | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sonnet | 10 | 1/1 | 10/10 | 0 | 0 | 0.0% [0.0%, 27.8%] | $0.39 / $0.39 |
| Luna | 10 | 1/1 | 10/10 | 0 | 0 | 0.0% [0.0%, 27.8%] | $0.04 / $0.04 |
| DeepSeek | 10 | 0/1 | 7/10 | 0 | 0 | 0.0% [0.0%, 35.4%] | $0.08 / $0.12 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | — | — | — | — |
| Sol | — | — | — | — | — |
| Sonnet | — | — | — | —; n=10 | —; n=7 |
| Luna | — | — | —; n=10 | — | —; n=7 |
| DeepSeek | — | — | —; n=7 | —; n=7 | — |

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 3 not applicable; Luna: 0 partial, 0 not applicable; DeepSeek: 0 partial, 0 not applicable.

## Lean Pool

Full-pass reference: **10 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sol | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sonnet | 10 | 1/1 | 10/10 | 4 | 4 | 40.0% [16.8%, 68.7%] | $1.10 / $1.10 |
| Luna | 10 | 1/1 | 10/10 | 0 | 0 | 0.0% [0.0%, 27.8%] | $0.06 / $0.06 |
| DeepSeek | 10 | 0/1 | 7/10 | 3 | 3 | 42.9% [15.8%, 75.0%] | $0.12 / $0.17 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | — | — | — | — |
| Sol | — | — | — | — | — |
| Sonnet | — | — | — | —; n=10 | 0.09 [—]; n=7 |
| Luna | — | — | —; n=10 | — | —; n=7 |
| DeepSeek | — | — | 0.09 [—]; n=7 | —; n=7 | — |

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 1 not applicable; Luna: 0 partial, 0 not applicable; DeepSeek: 0 partial, 0 not applicable.

## OpenAI Math

Full-pass reference: **100 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 100 | 1/1 | 100/100 | 7 | 7 | 7.0% [3.4%, 13.7%] | $15.66 / $15.66 |
| Sol | 100 | 1/1 | 100/100 | 1 | 1 | 1.0% [0.2%, 5.4%] | $8.47 / $8.47 |
| Sonnet | 100 | 1/1 | 100/100 | 6 | 6 | 6.0% [2.8%, 12.5%] | $6.80 / $6.80 |
| Luna | 100 | 1/1 | 100/100 | 5 | 5 | 5.0% [2.2%, 11.2%] | $0.50 / $0.50 |
| DeepSeek | 10 | 0/1 | 7/10 | 1 | 1 | 14.3% [2.6%, 51.3%] | $0.06 / $0.80 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | 0.37 [—]; n=100 | 0.59 [0.18, 0.89]; n=100 | 0.12 [-0.08, 0.45]; n=100 | 1.00 [—]; n=7 |
| Sol | 0.37 [—]; n=100 | — | 0.40 [—]; n=100 | 0.44 [—]; n=100 | 1.00 [—]; n=7 |
| Sonnet | 0.59 [0.18, 0.89]; n=100 | 0.40 [—]; n=100 | — | 0.14 [-0.07, 0.48]; n=100 | 1.00 [—]; n=7 |
| Luna | 0.12 [-0.08, 0.45]; n=100 | 0.44 [—]; n=100 | 0.14 [-0.07, 0.48]; n=100 | — | 1.00 [—]; n=7 |
| DeepSeek | 1.00 [—]; n=7 | 1.00 [—]; n=7 | 1.00 [—]; n=7 | 1.00 [—]; n=7 | — |

Coverage annotations: Opus: 0 partial, 49 not applicable; Sol: 0 partial, 22 not applicable; Sonnet: 0 partial, 39 not applicable; Luna: 0 partial, 1 not applicable; DeepSeek: 0 partial, 2 not applicable.
