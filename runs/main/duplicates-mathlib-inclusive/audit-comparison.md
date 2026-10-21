# duplicates-mathlib-inclusive

Generated 2026-10-21T11:05:04+00:00 · [Methods and notation](../../../AUDIT_METHODS.md) · 2,000 bootstrap draws.

Opus uses the earlier prompt on four libraries, without Mathlib targets.

## Library comparison

| Library | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Mathlib | — | 689/1000<br>68.9% [66.0%, 71.7%] | 263/1000<br>26.3% [23.7%, 29.1%] | 596/1000<br>59.6% [56.5%, 62.6%] | — |
| Tau Ceti | 50/1000<br>5.0% [3.8%, 6.5%] | 142/1000<br>14.2% [12.2%, 16.5%] | 35/1000<br>3.5% [2.5%, 4.8%] | 150/1000<br>15.0% [12.9%, 17.3%] | — |
| Formal Frontier | 46/1000<br>4.6% [3.5%, 6.1%] | 212/1000<br>21.2% [18.8%, 23.8%] | 45/1000<br>4.5% [3.4%, 6.0%] | 229/1000<br>22.9% [20.4%, 25.6%] | — |
| Lean Pool | 68/1000<br>6.8% [5.4%, 8.5%] | 149/1000<br>14.9% [12.8%, 17.2%] | 58/1000<br>5.8% [4.5%, 7.4%] | 147/1000<br>14.7% [12.6%, 17.0%] | — |
| FLT (Anthropic) | 137/1000<br>13.7% [11.7%, 16.0%] | 255/1000<br>25.5% [22.9%, 28.3%] | 118/1000<br>11.8% [9.9%, 13.9%] | 230/1000<br>23.0% [20.5%, 25.7%] | — |
| OpenAI Math | 1/22<br>4.5% [0.8%, 21.8%] | 2/70<br>2.9% [0.8%, 9.8%] | 2/41<br>4.9% [1.3%, 16.1%] | 2/48<br>4.2% [1.2%, 14.0%] | — |

## All libraries

Full-pass reference: **5000 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 4100 | 0/1 | 4022/4100 | 302 | 302 | 7.5% [6.7%, 8.4%] | $217.81 / $270.77 |
| Sol | 5100 | 0/1 | 5070/5100 | 1449 | 1449 | 28.6% [27.4%, 29.8%] | $324.01 / $319.54 |
| Sonnet | 5100 | 0/1 | 5041/5100 | 521 | 521 | 10.3% [9.5%, 11.2%] | $126.30 / $125.28 |
| Luna | 5100 | 0/1 | 5048/5100 | 1354 | 1354 | 26.8% [25.6%, 28.1%] | $16.16 / $16.00 |
| DeepSeek | 600 | 0/1 | 0/600 | 0 | 0 | — | $0.00 / — |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | 0.57 [0.54, 0.60]; n=4022 | 0.74 [0.70, 0.78]; n=4022 | 0.54 [0.51, 0.58]; n=4022 | — |
| Sol | 0.57 [0.54, 0.60]; n=4022 | — | 0.48 [0.46, 0.50]; n=5041 | 0.69 [0.67, 0.71]; n=5048 | — |
| Sonnet | 0.74 [0.70, 0.78]; n=4022 | 0.48 [0.46, 0.50]; n=5041 | — | 0.50 [0.48, 0.53]; n=5041 | — |
| Luna | 0.54 [0.51, 0.58]; n=4022 | 0.69 [0.67, 0.71]; n=5048 | 0.50 [0.48, 0.53]; n=5041 | — | — |
| DeepSeek | — | — | — | — | — |

## Mathlib

Full-pass reference: **1000 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 0 | 0/1 | 0/0 | 0 | 0 | — | $0.00 / — |
| Sol | 1000 | 1/1 | 1000/1000 | 689 | 689 | 68.9% [66.0%, 71.7%] | $54.38 / $54.38 |
| Sonnet | 1000 | 1/1 | 1000/1000 | 263 | 263 | 26.3% [23.7%, 29.1%] | $30.36 / $30.36 |
| Luna | 1000 | 1/1 | 1000/1000 | 596 | 596 | 59.6% [56.5%, 62.6%] | $2.71 / $2.71 |
| DeepSeek | 100 | 0/1 | 0/100 | 0 | 0 | — | $0.00 / — |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | — | — | — | — |
| Sol | — | — | 0.35 [0.31, 0.39]; n=1000 | 0.56 [0.51, 0.61]; n=1000 | — |
| Sonnet | — | 0.35 [0.31, 0.39]; n=1000 | — | 0.40 [0.36, 0.44]; n=1000 | — |
| Luna | — | 0.56 [0.51, 0.61]; n=1000 | 0.40 [0.36, 0.44]; n=1000 | — | — |
| DeepSeek | — | — | — | — | — |

## Tau Ceti

Full-pass reference: **1000 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 1000 | 1/1 | 1000/1000 | 50 | 50 | 5.0% [3.8%, 6.5%] | $49.56 / $49.56 |
| Sol | 1000 | 1/1 | 1000/1000 | 142 | 142 | 14.2% [12.2%, 16.5%] | $64.21 / $64.21 |
| Sonnet | 1000 | 1/1 | 1000/1000 | 35 | 35 | 3.5% [2.5%, 4.8%] | $20.80 / $20.80 |
| Luna | 1000 | 1/1 | 1000/1000 | 150 | 150 | 15.0% [12.9%, 17.3%] | $3.27 / $3.27 |
| DeepSeek | 100 | 0/1 | 0/100 | 0 | 0 | — | $0.00 / — |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | 0.55 [0.48, 0.62]; n=1000 | 0.66 [0.53, 0.76]; n=1000 | 0.51 [0.44, 0.58]; n=1000 | — |
| Sol | 0.55 [0.48, 0.62]; n=1000 | — | 0.45 [0.37, 0.53]; n=1000 | 0.64 [0.57, 0.71]; n=1000 | — |
| Sonnet | 0.66 [0.53, 0.76]; n=1000 | 0.45 [0.37, 0.53]; n=1000 | — | 0.41 [0.33, 0.48]; n=1000 | — |
| Luna | 0.51 [0.44, 0.58]; n=1000 | 0.64 [0.57, 0.71]; n=1000 | 0.41 [0.33, 0.48]; n=1000 | — | — |
| DeepSeek | — | — | — | — | — |

## Formal Frontier

Full-pass reference: **1000 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 1000 | 1/1 | 1000/1000 | 46 | 46 | 4.6% [3.5%, 6.1%] | $56.04 / $56.04 |
| Sol | 1000 | 1/1 | 1000/1000 | 212 | 212 | 21.2% [18.8%, 23.8%] | $67.53 / $67.53 |
| Sonnet | 1000 | 1/1 | 1000/1000 | 45 | 45 | 4.5% [3.4%, 6.0%] | $25.75 / $25.75 |
| Luna | 1000 | 1/1 | 1000/1000 | 229 | 229 | 22.9% [20.4%, 25.6%] | $3.55 / $3.55 |
| DeepSeek | 100 | 0/1 | 0/100 | 0 | 0 | — | $0.00 / — |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | 0.41 [0.35, 0.47]; n=1000 | 0.67 [0.54, 0.77]; n=1000 | 0.39 [0.33, 0.45]; n=1000 | — |
| Sol | 0.41 [0.35, 0.47]; n=1000 | — | 0.30 [0.22, 0.37]; n=1000 | 0.58 [0.52, 0.64]; n=1000 | — |
| Sonnet | 0.67 [0.54, 0.77]; n=1000 | 0.30 [0.22, 0.37]; n=1000 | — | 0.40 [0.34, 0.45]; n=1000 | — |
| Luna | 0.39 [0.33, 0.45]; n=1000 | 0.58 [0.52, 0.64]; n=1000 | 0.40 [0.34, 0.45]; n=1000 | — | — |
| DeepSeek | — | — | — | — | — |

## Lean Pool

Full-pass reference: **1000 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 1000 | 1/1 | 1000/1000 | 68 | 68 | 6.8% [5.4%, 8.5%] | $40.48 / $40.48 |
| Sol | 1000 | 1/1 | 1000/1000 | 149 | 149 | 14.9% [12.8%, 17.2%] | $60.29 / $60.29 |
| Sonnet | 1000 | 1/1 | 1000/1000 | 58 | 58 | 5.8% [4.5%, 7.4%] | $17.79 / $17.79 |
| Luna | 1000 | 1/1 | 1000/1000 | 147 | 147 | 14.7% [12.6%, 17.0%] | $2.88 / $2.88 |
| DeepSeek | 100 | 0/1 | 0/100 | 0 | 0 | — | $0.00 / — |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | 0.62 [0.55, 0.69]; n=1000 | 0.82 [0.74, 0.88]; n=1000 | 0.62 [0.55, 0.68]; n=1000 | — |
| Sol | 0.62 [0.55, 0.69]; n=1000 | — | 0.57 [0.50, 0.63]; n=1000 | 0.74 [0.68, 0.80]; n=1000 | — |
| Sonnet | 0.82 [0.74, 0.88]; n=1000 | 0.57 [0.50, 0.63]; n=1000 | — | 0.53 [0.45, 0.60]; n=1000 | — |
| Luna | 0.62 [0.55, 0.68]; n=1000 | 0.74 [0.68, 0.80]; n=1000 | 0.53 [0.45, 0.60]; n=1000 | — | — |
| DeepSeek | — | — | — | — | — |

## FLT (Anthropic)

Full-pass reference: **1000 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 1000 | 1/1 | 1000/1000 | 137 | 137 | 13.7% [11.7%, 16.0%] | $70.21 / $70.21 |
| Sol | 1000 | 1/1 | 1000/1000 | 255 | 255 | 25.5% [22.9%, 28.3%] | $73.09 / $73.09 |
| Sonnet | 1000 | 1/1 | 1000/1000 | 118 | 118 | 11.8% [9.9%, 13.9%] | $30.27 / $30.27 |
| Luna | 1000 | 1/1 | 1000/1000 | 230 | 230 | 23.0% [20.5%, 25.7%] | $3.58 / $3.58 |
| DeepSeek | 100 | 0/1 | 0/100 | 0 | 0 | — | $0.00 / — |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | 0.65 [0.60, 0.70]; n=1000 | 0.75 [0.68, 0.80]; n=1000 | 0.64 [0.58, 0.69]; n=1000 | — |
| Sol | 0.65 [0.60, 0.70]; n=1000 | — | 0.53 [0.47, 0.59]; n=1000 | 0.70 [0.65, 0.75]; n=1000 | — |
| Sonnet | 0.75 [0.68, 0.80]; n=1000 | 0.53 [0.47, 0.59]; n=1000 | — | 0.58 [0.52, 0.64]; n=1000 | — |
| Luna | 0.64 [0.58, 0.69]; n=1000 | 0.70 [0.65, 0.75]; n=1000 | 0.58 [0.52, 0.64]; n=1000 | — | — |
| DeepSeek | — | — | — | — | — |

## OpenAI Math

Full-pass reference: **0 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 100 | 0/1 | 22/100 | 1 | 1 | 4.5% [0.8%, 21.8%] | $1.52 / $0.00 |
| Sol | 100 | 0/1 | 70/100 | 2 | 2 | 2.9% [0.8%, 9.8%] | $4.50 / $0.00 |
| Sonnet | 100 | 0/1 | 41/100 | 2 | 2 | 4.9% [1.3%, 16.1%] | $1.33 / $0.00 |
| Luna | 100 | 0/1 | 48/100 | 2 | 2 | 4.2% [1.2%, 14.0%] | $0.16 / $0.00 |
| DeepSeek | 100 | 0/1 | 0/100 | 0 | 0 | — | $0.00 / — |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | 1.00 [—]; n=22 | 1.00 [—]; n=22 | 1.00 [—]; n=22 | — |
| Sol | 1.00 [—]; n=22 | — | 0.70 [—]; n=41 | 0.70 [—]; n=48 | — |
| Sonnet | 1.00 [—]; n=22 | 0.70 [—]; n=41 | — | 1.00 [—]; n=41 | — |
| Luna | 1.00 [—]; n=22 | 0.70 [—]; n=48 | 1.00 [—]; n=41 | — | — |
| DeepSeek | — | — | — | — | — |
