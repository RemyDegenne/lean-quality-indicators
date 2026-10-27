# concept-reinvention

Generated 2026-10-27T19:59:47+00:00 · [Methods and notation](../../../AUDIT_METHODS.md) · 2,000 bootstrap draws.

**Not ready for use.** Appendix audit; excluded from main summaries and library-quality conclusions. [Assessment and retained results](../../../AUDIT_APPENDIX.md#concept-reinvention).

## Library comparison

| Library | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Mathlib | — | — | 28/372<br>7.5% [5.3%, 10.7%] | 0/10<br>0.0% [0.0%, 27.8%] | 3/10<br>30.0% [10.8%, 60.3%] |
| Tau Ceti | — | — | 9/372<br>2.4% [1.3%, 4.5%] | 0/10<br>0.0% [0.0%, 27.8%] | 0/10<br>0.0% [0.0%, 27.8%] |
| Formal Frontier | — | — | 30/372<br>8.1% [5.7%, 11.3%] | — | — |
| Lean Pool | — | — | 52/371<br>14.0% [10.9%, 17.9%] | 0/10<br>0.0% [0.0%, 27.8%] | 5/10<br>50.0% [23.7%, 76.3%] |
| FLT (Anthropic) | — | — | 56/372<br>15.1% [11.8%, 19.0%] | — | — |
| OpenAI Math | 7/100<br>7.0% [3.4%, 13.7%] | 1/100<br>1.0% [0.2%, 5.4%] | 25/372<br>6.7% [4.6%, 9.7%] | 5/100<br>5.0% [2.2%, 11.2%] | 2/10<br>20.0% [5.7%, 51.0%] |

## All libraries

Full-pass reference: **130 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 100 | 1/1 | 100/100 | 7 | 7 | 7.0% [3.4%, 13.7%] | $15.66 / $20.36 |
| Sol | 100 | 1/1 | 100/100 | 1 | 1 | 1.0% [0.2%, 5.4%] | $8.47 / $11.02 |
| Sonnet | 3000 | 0/1 | 2231/3000 | 200 | 200 | 9.0% [7.8%, 10.2%] | $155.15 / $9.04 |
| Luna | 130 | 1/1 | 130/130 | 5 | 5 | 3.8% [1.7%, 8.7%] | $0.65 / $0.65 |
| DeepSeek | 40 | 1/1 | 40/40 | 10 | 10 | 25.0% [14.2%, 40.2%] | $0.67 / $2.17 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | 0.37 [—]; n=100 | 0.59 [0.22, 0.88]; n=100 | 0.12 [-0.08, 0.45]; n=100 | 1.00 [—]; n=10 |
| Sol | 0.37 [—]; n=100 | — | 0.40 [—]; n=100 | 0.44 [—]; n=100 | 0.67 [—]; n=10 |
| Sonnet | 0.59 [0.22, 0.88]; n=100 | 0.40 [—]; n=100 | — | 0.07 [-0.08, 0.33]; n=130 | 0.72 [0.46, 0.94]; n=40 |
| Luna | 0.12 [-0.08, 0.45]; n=100 | 0.44 [—]; n=100 | 0.07 [-0.08, 0.33]; n=130 | — | 0.28 [—]; n=40 |
| DeepSeek | 1.00 [—]; n=10 | 0.67 [—]; n=10 | 0.72 [0.46, 0.94]; n=40 | 0.28 [—]; n=40 | — |

Coverage annotations: Opus: 0 partial, 49 not applicable; Sol: 0 partial, 22 not applicable; Sonnet: 2 partial, 642 not applicable; Luna: 0 partial, 1 not applicable; DeepSeek: 0 partial, 3 not applicable.

## Mathlib

Full-pass reference: **10 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sol | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sonnet | 500 | 0/1 | 372/500 | 28 | 28 | 7.5% [5.3%, 10.7%] | $19.80 / $0.53 |
| Luna | 10 | 1/1 | 10/10 | 0 | 0 | 0.0% [0.0%, 27.8%] | $0.05 / $0.05 |
| DeepSeek | 10 | 1/1 | 10/10 | 3 | 3 | 30.0% [10.8%, 60.3%] | $0.24 / $0.24 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | — | — | — | — |
| Sol | — | — | — | — | — |
| Sonnet | — | — | — | —; n=10 | 0.76 [—]; n=10 |
| Luna | — | — | —; n=10 | — | —; n=10 |
| DeepSeek | — | — | 0.76 [—]; n=10 | —; n=10 | — |

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 54 not applicable; Luna: 0 partial, 0 not applicable; DeepSeek: 0 partial, 0 not applicable.

## Tau Ceti

Full-pass reference: **10 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sol | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sonnet | 500 | 0/1 | 372/500 | 9 | 9 | 2.4% [1.3%, 4.5%] | $16.45 / $0.44 |
| Luna | 10 | 1/1 | 10/10 | 0 | 0 | 0.0% [0.0%, 27.8%] | $0.04 / $0.04 |
| DeepSeek | 10 | 1/1 | 10/10 | 0 | 0 | 0.0% [0.0%, 27.8%] | $0.13 / $0.13 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | — | — | — | — |
| Sol | — | — | — | — | — |
| Sonnet | — | — | — | —; n=10 | —; n=10 |
| Luna | — | — | —; n=10 | — | —; n=10 |
| DeepSeek | — | — | —; n=10 | —; n=10 | — |

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 124 not applicable; Luna: 0 partial, 0 not applicable; DeepSeek: 0 partial, 0 not applicable.

## Formal Frontier

Full-pass reference: **500 targets** (planned; no completed pass yet).

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sol | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sonnet | 500 | 0/1 | 372/500 | 30 | 30 | 8.1% [5.7%, 11.3%] | $23.12 / $31.08 |
| Luna | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| DeepSeek | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | — | — | — | — |
| Sol | — | — | — | — | — |
| Sonnet | — | — | — | — | — |
| Luna | — | — | — | — | — |
| DeepSeek | — | — | — | — | — |

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 97 not applicable; Luna: 0 partial, 0 not applicable; DeepSeek: 0 partial, 0 not applicable.

## Lean Pool

Full-pass reference: **10 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sol | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sonnet | 500 | 0/1 | 371/500 | 52 | 52 | 14.0% [10.9%, 17.9%] | $27.70 / $0.75 |
| Luna | 10 | 1/1 | 10/10 | 0 | 0 | 0.0% [0.0%, 27.8%] | $0.06 / $0.06 |
| DeepSeek | 10 | 1/1 | 10/10 | 5 | 5 | 50.0% [23.7%, 76.3%] | $0.19 / $0.19 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | — | — | — | — |
| Sol | — | — | — | — | — |
| Sonnet | — | — | — | —; n=10 | 0.41 [-0.25, 0.82]; n=10 |
| Luna | — | — | —; n=10 | — | —; n=10 |
| DeepSeek | — | — | 0.41 [-0.25, 0.82]; n=10 | —; n=10 | — |

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 1 partial, 106 not applicable; Luna: 0 partial, 0 not applicable; DeepSeek: 0 partial, 0 not applicable.

## FLT (Anthropic)

Full-pass reference: **500 targets** (planned; no completed pass yet).

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sol | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sonnet | 500 | 0/1 | 372/500 | 56 | 56 | 15.1% [11.8%, 19.0%] | $41.27 / $55.47 |
| Luna | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| DeepSeek | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | — | — | — | — |
| Sol | — | — | — | — | — |
| Sonnet | — | — | — | — | — |
| Luna | — | — | — | — | — |
| DeepSeek | — | — | — | — | — |

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 1 partial, 124 not applicable; Luna: 0 partial, 0 not applicable; DeepSeek: 0 partial, 0 not applicable.

## OpenAI Math

Full-pass reference: **100 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 100 | 1/1 | 100/100 | 7 | 7 | 7.0% [3.4%, 13.7%] | $15.66 / $15.66 |
| Sol | 100 | 1/1 | 100/100 | 1 | 1 | 1.0% [0.2%, 5.4%] | $8.47 / $8.47 |
| Sonnet | 500 | 0/1 | 372/500 | 25 | 25 | 6.7% [4.6%, 9.7%] | $26.80 / $7.20 |
| Luna | 100 | 1/1 | 100/100 | 5 | 5 | 5.0% [2.2%, 11.2%] | $0.50 / $0.50 |
| DeepSeek | 10 | 1/1 | 10/10 | 2 | 2 | 20.0% [5.7%, 51.0%] | $0.11 / $1.08 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | 0.37 [—]; n=100 | 0.59 [0.18, 0.89]; n=100 | 0.12 [-0.08, 0.45]; n=100 | 1.00 [—]; n=10 |
| Sol | 0.37 [—]; n=100 | — | 0.40 [—]; n=100 | 0.44 [—]; n=100 | 0.67 [—]; n=10 |
| Sonnet | 0.59 [0.18, 0.89]; n=100 | 0.40 [—]; n=100 | — | 0.14 [-0.07, 0.48]; n=100 | 1.00 [—]; n=10 |
| Luna | 0.12 [-0.08, 0.45]; n=100 | 0.44 [—]; n=100 | 0.14 [-0.07, 0.48]; n=100 | — | 0.67 [—]; n=10 |
| DeepSeek | 1.00 [—]; n=10 | 0.67 [—]; n=10 | 1.00 [—]; n=10 | 0.67 [—]; n=10 | — |

Coverage annotations: Opus: 0 partial, 49 not applicable; Sol: 0 partial, 22 not applicable; Sonnet: 0 partial, 137 not applicable; Luna: 0 partial, 1 not applicable; DeepSeek: 0 partial, 3 not applicable.
