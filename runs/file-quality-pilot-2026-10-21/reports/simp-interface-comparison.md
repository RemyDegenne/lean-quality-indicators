# simp-interface

Generated 2026-10-27T16:02:58+00:00 · [Methods and notation](../../../AUDIT_METHODS.md) · 2,000 bootstrap draws.

**Not ready for use.** Appendix audit; excluded from main summaries and library-quality conclusions. [Assessment and retained results](../../../AUDIT_APPENDIX.md#simp-interface).

## Library comparison

| Library | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Mathlib | — | — | 170/372<br>45.7% [40.7%, 50.8%] | 4/10<br>40.0% [16.8%, 68.7%] | 7/10<br>70.0% [39.7%, 89.2%] |
| Tau Ceti | — | — | 165/372<br>44.4% [39.4%, 49.4%] | 1/10<br>10.0% [1.8%, 40.4%] | 3/10<br>30.0% [10.8%, 60.3%] |
| Formal Frontier | — | — | 200/370<br>54.1% [49.0%, 59.1%] | — | — |
| Lean Pool | — | — | 226/371<br>60.9% [55.9%, 65.7%] | 6/10<br>60.0% [31.3%, 83.2%] | 9/10<br>90.0% [59.6%, 98.2%] |
| FLT (Anthropic) | — | — | 168/370<br>45.4% [40.4%, 50.5%] | — | — |
| OpenAI Math | 45/100<br>45.0% [35.6%, 54.8%] | 31/100<br>31.0% [22.8%, 40.6%] | 211/371<br>56.9% [51.8%, 61.8%] | 29/100<br>29.0% [21.0%, 38.5%] | 9/10<br>90.0% [59.6%, 98.2%] |

## All libraries

Full-pass reference: **130 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 100 | 1/1 | 100/100 | 45 | 45 | 45.0% [35.6%, 54.8%] | $24.70 / $32.11 |
| Sol | 100 | 1/1 | 100/100 | 31 | 31 | 31.0% [22.8%, 40.6%] | $9.98 / $12.97 |
| Sonnet | 3000 | 0/1 | 2226/3000 | 1140 | 1140 | 51.2% [49.1%, 53.3%] | $229.55 / $13.41 |
| Luna | 130 | 1/1 | 130/130 | 40 | 40 | 30.8% [23.5%, 39.2%] | $0.59 / $0.59 |
| DeepSeek | 40 | 1/1 | 40/40 | 28 | 28 | 70.0% [54.6%, 81.9%] | $1.12 / $3.65 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | 0.57 [0.39, 0.71]; n=100 | 0.58 [0.41, 0.71]; n=100 | 0.40 [0.21, 0.56]; n=100 | 0.51 [—]; n=10 |
| Sol | 0.57 [0.39, 0.71]; n=100 | — | 0.56 [0.44, 0.69]; n=100 | 0.52 [0.34, 0.70]; n=100 | 0.22 [—]; n=10 |
| Sonnet | 0.58 [0.41, 0.71]; n=100 | 0.56 [0.44, 0.69]; n=100 | — | 0.30 [0.15, 0.46]; n=130 | 0.55 [0.30, 0.77]; n=40 |
| Luna | 0.40 [0.21, 0.56]; n=100 | 0.52 [0.34, 0.70]; n=100 | 0.30 [0.15, 0.46]; n=130 | — | 0.28 [0.00, 0.53]; n=40 |
| DeepSeek | 0.51 [—]; n=10 | 0.22 [—]; n=10 | 0.55 [0.30, 0.77]; n=40 | 0.28 [0.00, 0.53]; n=40 | — |

Coverage annotations: Opus: 0 partial, 19 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 7 partial, 158 not applicable; Luna: 0 partial, 1 not applicable; DeepSeek: 0 partial, 1 not applicable.

## Mathlib

Full-pass reference: **10 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sol | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sonnet | 500 | 0/1 | 372/500 | 170 | 170 | 45.7% [40.7%, 50.8%] | $30.27 / $0.81 |
| Luna | 10 | 1/1 | 10/10 | 4 | 4 | 40.0% [16.8%, 68.7%] | $0.05 / $0.05 |
| DeepSeek | 10 | 1/1 | 10/10 | 7 | 7 | 70.0% [39.7%, 89.2%] | $0.29 / $0.29 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | — | — | — | — |
| Sol | — | — | — | — | — |
| Sonnet | — | — | — | 0.58 [0.00, 1.00]; n=10 | 0.53 [—]; n=10 |
| Luna | — | — | 0.58 [0.00, 1.00]; n=10 | — | 0.09 [—]; n=10 |
| DeepSeek | — | — | 0.53 [—]; n=10 | 0.09 [—]; n=10 | — |

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 11 not applicable; Luna: 0 partial, 0 not applicable; DeepSeek: 0 partial, 1 not applicable.

## Tau Ceti

Full-pass reference: **10 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sol | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sonnet | 500 | 0/1 | 372/500 | 165 | 165 | 44.4% [39.4%, 49.4%] | $33.71 / $0.91 |
| Luna | 10 | 1/1 | 10/10 | 1 | 1 | 10.0% [1.8%, 40.4%] | $0.05 / $0.05 |
| DeepSeek | 10 | 1/1 | 10/10 | 3 | 3 | 30.0% [10.8%, 60.3%] | $0.26 / $0.26 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | — | — | — | — |
| Sol | — | — | — | — | — |
| Sonnet | — | — | — | -0.22 [—]; n=10 | 0.52 [—]; n=10 |
| Luna | — | — | -0.22 [—]; n=10 | — | -0.22 [—]; n=10 |
| DeepSeek | — | — | 0.52 [—]; n=10 | -0.22 [—]; n=10 | — |

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 20 not applicable; Luna: 0 partial, 0 not applicable; DeepSeek: 0 partial, 0 not applicable.

## Formal Frontier

Full-pass reference: **500 targets** (planned; no completed pass yet).

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sol | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sonnet | 500 | 0/1 | 370/500 | 200 | 200 | 54.1% [49.0%, 59.1%] | $32.72 / $44.21 |
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

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 22 not applicable; Luna: 0 partial, 0 not applicable; DeepSeek: 0 partial, 0 not applicable.

## Lean Pool

Full-pass reference: **10 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sol | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sonnet | 500 | 0/1 | 371/500 | 226 | 226 | 60.9% [55.9%, 65.7%] | $42.46 / $1.14 |
| Luna | 10 | 1/1 | 10/10 | 6 | 6 | 60.0% [31.3%, 83.2%] | $0.06 / $0.06 |
| DeepSeek | 10 | 1/1 | 10/10 | 9 | 9 | 90.0% [59.6%, 98.2%] | $0.33 / $0.33 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | — | — | — | — |
| Sol | — | — | — | — | — |
| Sonnet | — | — | — | 0.58 [-0.17, 1.00]; n=10 | 0.41 [—]; n=10 |
| Luna | — | — | 0.58 [-0.17, 1.00]; n=10 | — | 0.41 [—]; n=10 |
| DeepSeek | — | — | 0.41 [—]; n=10 | 0.41 [—]; n=10 | — |

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 3 partial, 22 not applicable; Luna: 0 partial, 0 not applicable; DeepSeek: 0 partial, 0 not applicable.

## FLT (Anthropic)

Full-pass reference: **500 targets** (planned; no completed pass yet).

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sol | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sonnet | 500 | 0/1 | 370/500 | 168 | 168 | 45.4% [40.4%, 50.5%] | $49.13 / $66.39 |
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

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 4 partial, 53 not applicable; Luna: 0 partial, 0 not applicable; DeepSeek: 0 partial, 0 not applicable.

## OpenAI Math

Full-pass reference: **100 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 100 | 1/1 | 100/100 | 45 | 45 | 45.0% [35.6%, 54.8%] | $24.70 / $24.70 |
| Sol | 100 | 1/1 | 100/100 | 31 | 31 | 31.0% [22.8%, 40.6%] | $9.98 / $9.98 |
| Sonnet | 500 | 0/1 | 371/500 | 211 | 211 | 56.9% [51.8%, 61.8%] | $41.27 / $11.12 |
| Luna | 100 | 1/1 | 100/100 | 29 | 29 | 29.0% [21.0%, 38.5%] | $0.44 / $0.44 |
| DeepSeek | 10 | 1/1 | 10/10 | 9 | 9 | 90.0% [59.6%, 98.2%] | $0.24 / $2.37 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | 0.57 [0.41, 0.71]; n=100 | 0.58 [0.41, 0.72]; n=100 | 0.40 [0.21, 0.58]; n=100 | 0.51 [—]; n=10 |
| Sol | 0.57 [0.41, 0.71]; n=100 | — | 0.56 [0.43, 0.69]; n=100 | 0.52 [0.33, 0.70]; n=100 | 0.22 [—]; n=10 |
| Sonnet | 0.58 [0.41, 0.72]; n=100 | 0.56 [0.43, 0.69]; n=100 | — | 0.27 [0.08, 0.44]; n=100 | 0.51 [—]; n=10 |
| Luna | 0.40 [0.21, 0.58]; n=100 | 0.52 [0.33, 0.70]; n=100 | 0.27 [0.08, 0.44]; n=100 | — | 0.27 [—]; n=10 |
| DeepSeek | 0.51 [—]; n=10 | 0.22 [—]; n=10 | 0.51 [—]; n=10 | 0.27 [—]; n=10 | — |

Coverage annotations: Opus: 0 partial, 19 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 30 not applicable; Luna: 0 partial, 1 not applicable; DeepSeek: 0 partial, 0 not applicable.
