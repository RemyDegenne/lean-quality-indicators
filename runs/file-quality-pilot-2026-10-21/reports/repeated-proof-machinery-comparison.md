# repeated-proof-machinery

Generated 2026-10-27T20:10:37+00:00 · [Methods and notation](../../../AUDIT_METHODS.md) · 2,000 bootstrap draws.

[Separate validation: 20 flagged and 10 unflagged targets per library](../../repeated-machinery-validation-2026-10-27/validation-report.md). These checks do not enter the first-pass counts.

## Library comparison

| Library | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Mathlib | — | — | 60/372<br>16.1% [12.7%, 20.2%] | 2/10<br>20.0% [5.7%, 51.0%] | 2/10<br>20.0% [5.7%, 51.0%] |
| Tau Ceti | — | — | 64/372<br>17.2% [13.7%, 21.4%] | 0/10<br>0.0% [0.0%, 27.8%] | 3/10<br>30.0% [10.8%, 60.3%] |
| Formal Frontier | — | — | 128/372<br>34.4% [29.8%, 39.4%] | — | — |
| Lean Pool | — | — | 180/372<br>48.4% [43.4%, 53.5%] | 3/10<br>30.0% [10.8%, 60.3%] | 7/10<br>70.0% [39.7%, 89.2%] |
| FLT (Anthropic) | — | — | 189/372<br>50.8% [45.7%, 55.9%] | — | — |
| OpenAI Math | 48/100<br>48.0% [38.5%, 57.7%] | 20/100<br>20.0% [13.3%, 28.9%] | 154/372<br>41.4% [36.5%, 46.5%] | 20/100<br>20.0% [13.3%, 28.9%] | 5/10<br>50.0% [23.7%, 76.3%] |
| CFSG (AxiomMath) | — | — | 158/295<br>53.6% [47.9%, 59.2%] | — | — |

## All libraries

Full-pass reference: **130 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 100 | 1/1 | 100/100 | 48 | 48 | 48.0% [38.5%, 57.7%] | $26.18 / $34.04 |
| Sol | 100 | 1/1 | 100/100 | 20 | 20 | 20.0% [13.3%, 28.9%] | $8.15 / $10.60 |
| Sonnet | 3300 | 0/1 | 2527/3300 | 933 | 933 | 36.9% [35.1%, 38.8%] | $218.50 / $11.24 |
| Luna | 130 | 1/1 | 130/130 | 25 | 25 | 19.2% [13.4%, 26.8%] | $0.46 / $0.46 |
| DeepSeek | 40 | 1/1 | 40/40 | 17 | 17 | 42.5% [28.5%, 57.8%] | $0.55 / $1.79 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | 0.42 [0.26, 0.56]; n=100 | 0.69 [0.55, 0.82]; n=100 | 0.32 [0.15, 0.49]; n=100 | 0.60 [0.00, 1.00]; n=10 |
| Sol | 0.42 [0.26, 0.56]; n=100 | — | 0.43 [0.24, 0.59]; n=100 | 0.50 [0.27, 0.69]; n=100 | 0.33 [—]; n=10 |
| Sonnet | 0.69 [0.55, 0.82]; n=100 | 0.43 [0.24, 0.59]; n=100 | — | 0.44 [0.27, 0.58]; n=130 | 0.70 [0.49, 0.90]; n=40 |
| Luna | 0.32 [0.15, 0.49]; n=100 | 0.50 [0.27, 0.69]; n=100 | 0.44 [0.27, 0.58]; n=130 | — | 0.54 [0.33, 0.72]; n=40 |
| DeepSeek | 0.60 [0.00, 1.00]; n=10 | 0.33 [—]; n=10 | 0.70 [0.49, 0.90]; n=40 | 0.54 [0.33, 0.72]; n=40 | — |

Coverage annotations: Opus: 0 partial, 1 not applicable; Sol: 0 partial, 1 not applicable; Sonnet: 7 partial, 28 not applicable; Luna: 0 partial, 0 not applicable; DeepSeek: 0 partial, 0 not applicable.

## Mathlib

Full-pass reference: **10 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sol | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sonnet | 500 | 0/1 | 372/500 | 60 | 60 | 16.1% [12.7%, 20.2%] | $17.58 / $0.47 |
| Luna | 10 | 1/1 | 10/10 | 2 | 2 | 20.0% [5.7%, 51.0%] | $0.03 / $0.03 |
| DeepSeek | 10 | 1/1 | 10/10 | 2 | 2 | 20.0% [5.7%, 51.0%] | $0.15 / $0.15 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | — | — | — | — |
| Sol | — | — | — | — | — |
| Sonnet | — | — | — | 1.00 [—]; n=10 | 1.00 [—]; n=10 |
| Luna | — | — | 1.00 [—]; n=10 | — | 1.00 [—]; n=10 |
| DeepSeek | — | — | 1.00 [—]; n=10 | 1.00 [—]; n=10 | — |

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 4 not applicable; Luna: 0 partial, 0 not applicable; DeepSeek: 0 partial, 0 not applicable.

## Tau Ceti

Full-pass reference: **10 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sol | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sonnet | 500 | 0/1 | 372/500 | 64 | 64 | 17.2% [13.7%, 21.4%] | $19.49 / $0.52 |
| Luna | 10 | 1/1 | 10/10 | 0 | 0 | 0.0% [0.0%, 27.8%] | $0.03 / $0.03 |
| DeepSeek | 10 | 1/1 | 10/10 | 3 | 3 | 30.0% [10.8%, 60.3%] | $0.13 / $0.13 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | — | — | — | — |
| Sol | — | — | — | — | — |
| Sonnet | — | — | — | —; n=10 | 0.22 [—]; n=10 |
| Luna | — | — | —; n=10 | — | —; n=10 |
| DeepSeek | — | — | 0.22 [—]; n=10 | —; n=10 | — |

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 2 not applicable; Luna: 0 partial, 0 not applicable; DeepSeek: 0 partial, 0 not applicable.

## Formal Frontier

Full-pass reference: **500 targets** (planned; no completed pass yet).

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sol | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sonnet | 500 | 0/1 | 372/500 | 128 | 128 | 34.4% [29.8%, 39.4%] | $22.68 / $30.48 |
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

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 0 not applicable; Luna: 0 partial, 0 not applicable; DeepSeek: 0 partial, 0 not applicable.

## Lean Pool

Full-pass reference: **10 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sol | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sonnet | 500 | 0/1 | 372/500 | 180 | 180 | 48.4% [43.4%, 53.5%] | $37.75 / $1.01 |
| Luna | 10 | 1/1 | 10/10 | 3 | 3 | 30.0% [10.8%, 60.3%] | $0.04 / $0.04 |
| DeepSeek | 10 | 1/1 | 10/10 | 7 | 7 | 70.0% [39.7%, 89.2%] | $0.16 / $0.16 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | — | — | — | — |
| Sol | — | — | — | — | — |
| Sonnet | — | — | — | 0.53 [—]; n=10 | 0.80 [—]; n=10 |
| Luna | — | — | 0.53 [—]; n=10 | — | 0.43 [—]; n=10 |
| DeepSeek | — | — | 0.80 [—]; n=10 | 0.43 [—]; n=10 | — |

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 3 partial, 9 not applicable; Luna: 0 partial, 0 not applicable; DeepSeek: 0 partial, 0 not applicable.

## FLT (Anthropic)

Full-pass reference: **500 targets** (planned; no completed pass yet).

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sol | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sonnet | 500 | 0/1 | 372/500 | 189 | 189 | 50.8% [45.7%, 55.9%] | $50.65 / $68.08 |
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

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 4 partial, 3 not applicable; Luna: 0 partial, 0 not applicable; DeepSeek: 0 partial, 0 not applicable.

## OpenAI Math

Full-pass reference: **100 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 100 | 1/1 | 100/100 | 48 | 48 | 48.0% [38.5%, 57.7%] | $26.18 / $26.18 |
| Sol | 100 | 1/1 | 100/100 | 20 | 20 | 20.0% [13.3%, 28.9%] | $8.15 / $8.15 |
| Sonnet | 500 | 0/1 | 372/500 | 154 | 154 | 41.4% [36.5%, 46.5%] | $37.99 / $10.21 |
| Luna | 100 | 1/1 | 100/100 | 20 | 20 | 20.0% [13.3%, 28.9%] | $0.36 / $0.36 |
| DeepSeek | 10 | 1/1 | 10/10 | 5 | 5 | 50.0% [23.7%, 76.3%] | $0.11 / $1.07 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | 0.42 [0.26, 0.56]; n=100 | 0.69 [0.55, 0.81]; n=100 | 0.32 [0.14, 0.49]; n=100 | 0.60 [0.00, 1.00]; n=10 |
| Sol | 0.42 [0.26, 0.56]; n=100 | — | 0.43 [0.25, 0.61]; n=100 | 0.50 [0.27, 0.70]; n=100 | 0.33 [—]; n=10 |
| Sonnet | 0.69 [0.55, 0.81]; n=100 | 0.43 [0.25, 0.61]; n=100 | — | 0.38 [0.19, 0.55]; n=100 | 0.65 [—]; n=10 |
| Luna | 0.32 [0.14, 0.49]; n=100 | 0.50 [0.27, 0.70]; n=100 | 0.38 [0.19, 0.55]; n=100 | — | 0.50 [—]; n=10 |
| DeepSeek | 0.60 [0.00, 1.00]; n=10 | 0.33 [—]; n=10 | 0.65 [—]; n=10 | 0.50 [—]; n=10 | — |

Coverage annotations: Opus: 0 partial, 1 not applicable; Sol: 0 partial, 1 not applicable; Sonnet: 0 partial, 5 not applicable; Luna: 0 partial, 0 not applicable; DeepSeek: 0 partial, 0 not applicable.

## CFSG (AxiomMath)

Full-pass reference: **30 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sol | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sonnet | 300 | 0/1 | 295/300 | 158 | 158 | 53.6% [47.9%, 59.2%] | $32.36 / $3.29 |
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

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 5 not applicable; Luna: 0 partial, 0 not applicable; DeepSeek: 0 partial, 0 not applicable.
