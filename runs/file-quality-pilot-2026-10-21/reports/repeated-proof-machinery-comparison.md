# repeated-proof-machinery

Generated 2026-10-22T00:29:25+00:00 · [Methods and notation](../../../AUDIT_METHODS.md) · 2,000 bootstrap draws.

## Library comparison

| Library | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Mathlib | — | — | 2/10<br>20.0% [5.7%, 51.0%] | 2/10<br>20.0% [5.7%, 51.0%] | 1/6<br>16.7% [3.0%, 56.4%] |
| Tau Ceti | — | — | 2/10<br>20.0% [5.7%, 51.0%] | 0/10<br>0.0% [0.0%, 27.8%] | 2/7<br>28.6% [8.2%, 64.1%] |
| Lean Pool | — | — | 6/10<br>60.0% [31.3%, 83.2%] | 3/10<br>30.0% [10.8%, 60.3%] | 5/7<br>71.4% [35.9%, 91.8%] |
| OpenAI Math | 48/100<br>48.0% [38.5%, 57.7%] | 20/100<br>20.0% [13.3%, 28.9%] | 38/100<br>38.0% [29.1%, 47.8%] | 20/100<br>20.0% [13.3%, 28.9%] | 4/7<br>57.1% [25.0%, 84.2%] |

## All libraries

Full-pass reference: **130 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 100 | 1/1 | 100/100 | 48 | 48 | 48.0% [38.5%, 57.7%] | $26.18 / $34.04 |
| Sol | 100 | 1/1 | 100/100 | 20 | 20 | 20.0% [13.3%, 28.9%] | $8.15 / $10.60 |
| Sonnet | 130 | 1/1 | 130/130 | 48 | 48 | 36.9% [29.1%, 45.5%] | $11.00 / $11.00 |
| Luna | 130 | 1/1 | 130/130 | 25 | 25 | 19.2% [13.4%, 26.8%] | $0.46 / $0.46 |
| DeepSeek | 40 | 0/1 | 27/40 | 12 | 12 | 44.4% [27.6%, 62.7%] | $0.38 / $1.83 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | 0.42 [0.26, 0.56]; n=100 | 0.69 [0.55, 0.82]; n=100 | 0.32 [0.15, 0.49]; n=100 | 0.42 [—]; n=7 |
| Sol | 0.42 [0.26, 0.56]; n=100 | — | 0.43 [0.24, 0.59]; n=100 | 0.50 [0.27, 0.69]; n=100 | 0.35 [—]; n=7 |
| Sonnet | 0.69 [0.55, 0.82]; n=100 | 0.43 [0.24, 0.59]; n=100 | — | 0.44 [0.27, 0.58]; n=130 | 0.70 [0.46, 0.93]; n=27 |
| Luna | 0.32 [0.15, 0.49]; n=100 | 0.50 [0.27, 0.69]; n=100 | 0.44 [0.27, 0.58]; n=130 | — | 0.53 [0.30, 0.77]; n=27 |
| DeepSeek | 0.42 [—]; n=7 | 0.35 [—]; n=7 | 0.70 [0.46, 0.93]; n=27 | 0.53 [0.30, 0.77]; n=27 | — |

Coverage annotations: Opus: 0 partial, 1 not applicable; Sol: 0 partial, 1 not applicable; Sonnet: 0 partial, 2 not applicable; Luna: 0 partial, 0 not applicable; DeepSeek: 0 partial, 0 not applicable.

## Mathlib

Full-pass reference: **10 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sol | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sonnet | 10 | 1/1 | 10/10 | 2 | 2 | 20.0% [5.7%, 51.0%] | $0.55 / $0.55 |
| Luna | 10 | 1/1 | 10/10 | 2 | 2 | 20.0% [5.7%, 51.0%] | $0.03 / $0.03 |
| DeepSeek | 10 | 0/1 | 6/10 | 1 | 1 | 16.7% [3.0%, 56.4%] | $0.10 / $0.16 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | — | — | — | — |
| Sol | — | — | — | — | — |
| Sonnet | — | — | — | 1.00 [—]; n=10 | 1.00 [—]; n=6 |
| Luna | — | — | 1.00 [—]; n=10 | — | 1.00 [—]; n=6 |
| DeepSeek | — | — | 1.00 [—]; n=6 | 1.00 [—]; n=6 | — |

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 1 not applicable; Luna: 0 partial, 0 not applicable; DeepSeek: 0 partial, 0 not applicable.

## Tau Ceti

Full-pass reference: **10 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sol | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sonnet | 10 | 1/1 | 10/10 | 2 | 2 | 20.0% [5.7%, 51.0%] | $0.46 / $0.46 |
| Luna | 10 | 1/1 | 10/10 | 0 | 0 | 0.0% [0.0%, 27.8%] | $0.03 / $0.03 |
| DeepSeek | 10 | 0/1 | 7/10 | 2 | 2 | 28.6% [8.2%, 64.1%] | $0.09 / $0.13 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | — | — | — | — |
| Sol | — | — | — | — | — |
| Sonnet | — | — | — | —; n=10 | 0.30 [—]; n=7 |
| Luna | — | — | —; n=10 | — | —; n=7 |
| DeepSeek | — | — | 0.30 [—]; n=7 | —; n=7 | — |

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 0 not applicable; Luna: 0 partial, 0 not applicable; DeepSeek: 0 partial, 0 not applicable.

## Lean Pool

Full-pass reference: **10 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sol | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sonnet | 10 | 1/1 | 10/10 | 6 | 6 | 60.0% [31.3%, 83.2%] | $1.05 / $1.05 |
| Luna | 10 | 1/1 | 10/10 | 3 | 3 | 30.0% [10.8%, 60.3%] | $0.04 / $0.04 |
| DeepSeek | 10 | 0/1 | 7/10 | 5 | 5 | 71.4% [35.9%, 91.8%] | $0.11 / $0.16 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | — | — | — | — |
| Sol | — | — | — | — | — |
| Sonnet | — | — | — | 0.53 [—]; n=10 | 1.00 [—]; n=7 |
| Luna | — | — | 0.53 [—]; n=10 | — | 0.40 [—]; n=7 |
| DeepSeek | — | — | 1.00 [—]; n=7 | 0.40 [—]; n=7 | — |

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 0 not applicable; Luna: 0 partial, 0 not applicable; DeepSeek: 0 partial, 0 not applicable.

## OpenAI Math

Full-pass reference: **100 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 100 | 1/1 | 100/100 | 48 | 48 | 48.0% [38.5%, 57.7%] | $26.18 / $26.18 |
| Sol | 100 | 1/1 | 100/100 | 20 | 20 | 20.0% [13.3%, 28.9%] | $8.15 / $8.15 |
| Sonnet | 100 | 1/1 | 100/100 | 38 | 38 | 38.0% [29.1%, 47.8%] | $8.94 / $8.94 |
| Luna | 100 | 1/1 | 100/100 | 20 | 20 | 20.0% [13.3%, 28.9%] | $0.36 / $0.36 |
| DeepSeek | 10 | 0/1 | 7/10 | 4 | 4 | 57.1% [25.0%, 84.2%] | $0.08 / $1.09 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | 0.42 [0.26, 0.56]; n=100 | 0.69 [0.55, 0.81]; n=100 | 0.32 [0.14, 0.49]; n=100 | 0.42 [—]; n=7 |
| Sol | 0.42 [0.26, 0.56]; n=100 | — | 0.43 [0.25, 0.61]; n=100 | 0.50 [0.27, 0.70]; n=100 | 0.35 [—]; n=7 |
| Sonnet | 0.69 [0.55, 0.81]; n=100 | 0.43 [0.25, 0.61]; n=100 | — | 0.38 [0.19, 0.55]; n=100 | 0.55 [—]; n=7 |
| Luna | 0.32 [0.14, 0.49]; n=100 | 0.50 [0.27, 0.70]; n=100 | 0.38 [0.19, 0.55]; n=100 | — | 0.55 [—]; n=7 |
| DeepSeek | 0.42 [—]; n=7 | 0.35 [—]; n=7 | 0.55 [—]; n=7 | 0.55 [—]; n=7 | — |

Coverage annotations: Opus: 0 partial, 1 not applicable; Sol: 0 partial, 1 not applicable; Sonnet: 0 partial, 1 not applicable; Luna: 0 partial, 0 not applicable; DeepSeek: 0 partial, 0 not applicable.
