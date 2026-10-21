# simp-interface

Generated 2026-10-21T21:31:52+00:00 · [Methods and notation](../../../AUDIT_METHODS.md) · 2,000 bootstrap draws.

## Library comparison

| Library | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Mathlib | — | — | 4/10<br>40.0% [16.8%, 68.7%] | 4/10<br>40.0% [16.8%, 68.7%] | — |
| Tau Ceti | — | — | 3/10<br>30.0% [10.8%, 60.3%] | 1/10<br>10.0% [1.8%, 40.4%] | — |
| Lean Pool | — | — | 6/10<br>60.0% [31.3%, 83.2%] | 6/10<br>60.0% [31.3%, 83.2%] | — |
| OpenAI Math | 45/100<br>45.0% [35.6%, 54.8%] | 31/100<br>31.0% [22.8%, 40.6%] | 55/100<br>55.0% [45.2%, 64.4%] | 29/100<br>29.0% [21.0%, 38.5%] | — |

## All libraries

Full-pass reference: **130 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 100 | 1/1 | 100/100 | 45 | 45 | 45.0% [35.6%, 54.8%] | $24.70 / $32.11 |
| Sol | 100 | 1/1 | 100/100 | 31 | 31 | 31.0% [22.8%, 40.6%] | $9.98 / $12.97 |
| Sonnet | 130 | 1/1 | 130/130 | 68 | 68 | 52.3% [43.8%, 60.7%] | $12.54 / $12.54 |
| Luna | 130 | 1/1 | 130/130 | 40 | 40 | 30.8% [23.5%, 39.2%] | $0.59 / $0.59 |
| DeepSeek | 40 | 0/1 | 0/40 | 0 | 0 | — | $0.00 / — |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | 0.57 [0.39, 0.71]; n=100 | 0.58 [0.41, 0.71]; n=100 | 0.40 [0.21, 0.56]; n=100 | — |
| Sol | 0.57 [0.39, 0.71]; n=100 | — | 0.56 [0.44, 0.69]; n=100 | 0.52 [0.34, 0.70]; n=100 | — |
| Sonnet | 0.58 [0.41, 0.71]; n=100 | 0.56 [0.44, 0.69]; n=100 | — | 0.30 [0.15, 0.46]; n=130 | — |
| Luna | 0.40 [0.21, 0.56]; n=100 | 0.52 [0.34, 0.70]; n=100 | 0.30 [0.15, 0.46]; n=130 | — | — |
| DeepSeek | — | — | — | — | — |

Coverage annotations: Opus: 0 partial, 19 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 13 not applicable; Luna: 0 partial, 1 not applicable; DeepSeek: 0 partial, 0 not applicable.

## Mathlib

Full-pass reference: **10 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sol | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sonnet | 10 | 1/1 | 10/10 | 4 | 4 | 40.0% [16.8%, 68.7%] | $0.68 / $0.68 |
| Luna | 10 | 1/1 | 10/10 | 4 | 4 | 40.0% [16.8%, 68.7%] | $0.05 / $0.05 |
| DeepSeek | 10 | 0/1 | 0/10 | 0 | 0 | — | $0.00 / — |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | — | — | — | — |
| Sol | — | — | — | — | — |
| Sonnet | — | — | — | 0.58 [0.00, 1.00]; n=10 | — |
| Luna | — | — | 0.58 [0.00, 1.00]; n=10 | — | — |
| DeepSeek | — | — | — | — | — |

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 1 not applicable; Luna: 0 partial, 0 not applicable; DeepSeek: 0 partial, 0 not applicable.

## Tau Ceti

Full-pass reference: **10 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sol | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sonnet | 10 | 1/1 | 10/10 | 3 | 3 | 30.0% [10.8%, 60.3%] | $0.68 / $0.68 |
| Luna | 10 | 1/1 | 10/10 | 1 | 1 | 10.0% [1.8%, 40.4%] | $0.05 / $0.05 |
| DeepSeek | 10 | 0/1 | 0/10 | 0 | 0 | — | $0.00 / — |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | — | — | — | — |
| Sol | — | — | — | — | — |
| Sonnet | — | — | — | -0.22 [—]; n=10 | — |
| Luna | — | — | -0.22 [—]; n=10 | — | — |
| DeepSeek | — | — | — | — | — |

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 0 not applicable; Luna: 0 partial, 0 not applicable; DeepSeek: 0 partial, 0 not applicable.

## Lean Pool

Full-pass reference: **10 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sol | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sonnet | 10 | 1/1 | 10/10 | 6 | 6 | 60.0% [31.3%, 83.2%] | $1.04 / $1.04 |
| Luna | 10 | 1/1 | 10/10 | 6 | 6 | 60.0% [31.3%, 83.2%] | $0.06 / $0.06 |
| DeepSeek | 10 | 0/1 | 0/10 | 0 | 0 | — | $0.00 / — |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | — | — | — | — |
| Sol | — | — | — | — | — |
| Sonnet | — | — | — | 0.58 [-0.17, 1.00]; n=10 | — |
| Luna | — | — | 0.58 [-0.17, 1.00]; n=10 | — | — |
| DeepSeek | — | — | — | — | — |

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 0 not applicable; Luna: 0 partial, 0 not applicable; DeepSeek: 0 partial, 0 not applicable.

## OpenAI Math

Full-pass reference: **100 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 100 | 1/1 | 100/100 | 45 | 45 | 45.0% [35.6%, 54.8%] | $24.70 / $24.70 |
| Sol | 100 | 1/1 | 100/100 | 31 | 31 | 31.0% [22.8%, 40.6%] | $9.98 / $9.98 |
| Sonnet | 100 | 1/1 | 100/100 | 55 | 55 | 55.0% [45.2%, 64.4%] | $10.15 / $10.15 |
| Luna | 100 | 1/1 | 100/100 | 29 | 29 | 29.0% [21.0%, 38.5%] | $0.44 / $0.44 |
| DeepSeek | 10 | 0/1 | 0/10 | 0 | 0 | — | $0.00 / — |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | 0.57 [0.41, 0.71]; n=100 | 0.58 [0.41, 0.72]; n=100 | 0.40 [0.21, 0.58]; n=100 | — |
| Sol | 0.57 [0.41, 0.71]; n=100 | — | 0.56 [0.43, 0.69]; n=100 | 0.52 [0.33, 0.70]; n=100 | — |
| Sonnet | 0.58 [0.41, 0.72]; n=100 | 0.56 [0.43, 0.69]; n=100 | — | 0.27 [0.08, 0.44]; n=100 | — |
| Luna | 0.40 [0.21, 0.58]; n=100 | 0.52 [0.33, 0.70]; n=100 | 0.27 [0.08, 0.44]; n=100 | — | — |
| DeepSeek | — | — | — | — | — |

Coverage annotations: Opus: 0 partial, 19 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 12 not applicable; Luna: 0 partial, 1 not applicable; DeepSeek: 0 partial, 0 not applicable.
