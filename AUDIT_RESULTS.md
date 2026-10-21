# Audit results

Generated 2026-10-21T07:24:43+00:00 · [Methods and notation](AUDIT_METHODS.md) · [Cost summary](runs/main/api-equivalent-costs.md).

## Combined summary

Union across **8 audits**: a target counts once per model if any audit flags it. First passes only; theorem and file samples are counted separately. Each rate uses only targets reviewed on **every contributing audit**; a dash means no such targets. [Aggregation details](AUDIT_METHODS.md#combined-summary).

### Theorem audits: library comparison

Contributing audits: [unnecessary-hypotheses](#unnecessary-hypotheses), [duplicates-mathlib-inclusive](#duplicates-mathlib-inclusive).

| Library | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Mathlib | — | 215/300<br>71.7% [66.3%, 76.5%] | 85/300<br>28.3% [23.5%, 33.7%] | 176/300<br>58.7% [53.0%, 64.1%] | — |
| Tau Ceti | 39/400<br>9.8% [7.2%, 13.1%] | 65/300<br>21.7% [17.4%, 26.7%] | 22/300<br>7.3% [4.9%, 10.9%] | 62/300<br>20.7% [16.5%, 25.6%] | — |
| Formal Frontier | 32/400<br>8.0% [5.7%, 11.1%] | 78/300<br>26.0% [21.4%, 31.2%] | 19/300<br>6.3% [4.1%, 9.7%] | 78/300<br>26.0% [21.4%, 31.2%] | — |
| Lean Pool | 83/400<br>20.8% [17.1%, 25.0%] | 95/300<br>31.7% [26.7%, 37.1%] | 55/300<br>18.3% [14.4%, 23.1%] | 87/300<br>29.0% [24.2%, 34.4%] | — |
| FLT (Anthropic) | 123/400<br>30.8% [26.4%, 35.4%] | 148/300<br>49.3% [43.7%, 55.0%] | 75/300<br>25.0% [20.4%, 30.2%] | 118/300<br>39.3% [34.0%, 45.0%] | — |
| OpenAI Math | 2/20<br>10.0% [2.8%, 30.1%] | 4/16<br>25.0% [10.2%, 49.5%] | 3/29<br>10.3% [3.6%, 26.4%] | 4/26<br>15.4% [6.1%, 33.5%] | — |

### File audits: library comparison

Contributing audits: [concept-reinvention](#concept-reinvention), [statement-generality](#statement-generality), [vacuity-and-misstatement](#vacuity-and-misstatement), [simp-interface](#simp-interface), [repeated-proof-machinery](#repeated-proof-machinery), [readable-proof-simplification](#readable-proof-simplification).

| Library | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Mathlib | — | — | 10/10<br>100.0% [72.2%, 100.0%] | 8/10<br>80.0% [49.0%, 94.3%] | — |
| Tau Ceti | — | — | 9/10<br>90.0% [59.6%, 98.2%] | 4/10<br>40.0% [16.8%, 68.7%] | — |
| Lean Pool | — | — | 9/10<br>90.0% [59.6%, 98.2%] | 8/10<br>80.0% [49.0%, 94.3%] | — |
| OpenAI Math | 17/19<br>89.5% [68.6%, 97.1%] | 12/14<br>85.7% [60.1%, 96.0%] | 25/28<br>89.3% [72.8%, 96.3%] | 17/25<br>68.0% [48.4%, 82.8%] | — |

### Model comparison

| Model | Audits with results | Theorems selected | Files selected | Audit passes done/planned | Theorems flagged / reviewed | Files flagged / reviewed | Judgments done/planned | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| Opus | 8/8 | 4500 | 100 | 1/9 | 279/1620 | 17/19 | 7655/8300 | $503.31 / $462.96 |
| Sol | 8/8 | 5100 | 100 | 1/9 | 605/1516 | 12/14 | 8123/8800 | $471.55 / $432.21 |
| Sonnet | 8/8 | 5100 | 130 | 1/9 | 259/1529 | 53/58 | 8409/8980 | $265.89 / $212.70 |
| Luna | 8/8 | 5100 | 130 | 1/9 | 525/1526 | 37/55 | 8385/8980 | $24.14 / $21.15 |
| DeepSeek | 1/8 | 600 | 40 | 0/8 | — | — | 1/1440 | $0.01 / — |

### Theorem union correlations

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | 0.92 [0.89, 0.95]; n=1500 | 0.67 [0.63, 0.71]; n=1216 | 0.80 [0.76, 0.84]; n=1220 | 0.55 [0.50, 0.60]; n=1220 | —; n=1 |
| Sol | 0.67 [0.63, 0.71]; n=1216 | 0.99 [0.97, 1.00]; n=1500 | 0.53 [0.50, 0.56]; n=1516 | 0.65 [0.61, 0.69]; n=1516 | —; n=1 |
| Sonnet | 0.80 [0.76, 0.84]; n=1220 | 0.53 [0.50, 0.56]; n=1516 | 0.87 [0.83, 0.92]; n=1500 | 0.51 [0.46, 0.55]; n=1526 | —; n=1 |
| Luna | 0.55 [0.50, 0.60]; n=1220 | 0.65 [0.61, 0.69]; n=1516 | 0.51 [0.46, 0.55]; n=1526 | 0.73 [0.66, 0.78]; n=1500 | —; n=1 |
| DeepSeek | —; n=1 | —; n=1 | —; n=1 | —; n=1 | — |

### File union correlations

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | 1.00 [—]; n=14 | 0.79 [—]; n=19 | 0.50 [—]; n=19 | — |
| Sol | 1.00 [—]; n=14 | — | 1.00 [—]; n=14 | 0.55 [—]; n=14 | — |
| Sonnet | 0.79 [—]; n=19 | 1.00 [—]; n=14 | — | 0.45 [0.24, 0.63]; n=55 | — |
| Luna | 0.50 [—]; n=19 | 0.55 [—]; n=14 | 0.45 [0.24, 0.63]; n=55 | — | — |
| DeepSeek | — | — | — | — | — |

## unnecessary-hypotheses

[Library breakdowns](runs/main/unnecessary-hypotheses/audit-comparison.md)

### Library comparison

| Library | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Mathlib | 15/400<br>3.8% [2.3%, 6.1%] | 12/300<br>4.0% [2.3%, 6.9%] | 6/300<br>2.0% [0.9%, 4.3%] | 12/300<br>4.0% [2.3%, 6.9%] | — |
| Tau Ceti | 23/400<br>5.8% [3.9%, 8.5%] | 19/300<br>6.3% [4.1%, 9.7%] | 12/300<br>4.0% [2.3%, 6.9%] | 19/300<br>6.3% [4.1%, 9.7%] | — |
| Formal Frontier | 17/400<br>4.2% [2.7%, 6.7%] | 18/300<br>6.0% [3.8%, 9.3%] | 12/300<br>4.0% [2.3%, 6.9%] | 15/300<br>5.0% [3.1%, 8.1%] | — |
| Lean Pool | 61/400<br>15.2% [12.1%, 19.1%] | 60/300<br>20.0% [15.9%, 24.9%] | 39/300<br>13.0% [9.7%, 17.3%] | 48/300<br>16.0% [12.3%, 20.6%] | — |
| FLT (Anthropic) | 82/400<br>20.5% [16.8%, 24.7%] | 78/300<br>26.0% [21.4%, 31.2%] | 52/300<br>17.3% [13.5%, 22.0%] | 61/300<br>20.3% [16.2%, 25.2%] | 0/1<br>0.0% [0.0%, 79.3%] |
| OpenAI Math | 1/20<br>5.0% [0.9%, 23.6%] | 3/16<br>18.8% [6.6%, 43.0%] | 1/29<br>3.4% [0.6%, 17.2%] | 3/26<br>11.5% [4.0%, 29.0%] | — |

### Model comparison

Full-pass reference: **2000 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 2100 | 1/2 | 3520/3600 | 349 | 206 | 9.9% [8.6%, 11.2%] | $255.80 / $145.34 |
| Sol | 1600 | 1/2 | 3016/3100 | 377 | 192 | 12.5% [11.0%, 14.3%] | $141.45 / $93.80 |
| Sonnet | 1600 | 1/2 | 3029/3100 | 246 | 138 | 8.0% [6.7%, 9.4%] | $106.56 / $70.36 |
| Luna | 1600 | 1/2 | 3026/3100 | 313 | 196 | 10.4% [8.9%, 12.0%] | $6.56 / $4.34 |
| DeepSeek | 600 | 0/1 | 1/600 | 0 | 0 | 0.0% [0.0%, 79.3%] | $0.01 / $13.87 |

#### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | 0.92 [0.89, 0.95]; n=1500 | 0.90 [0.87, 0.93]; n=1516 | 0.85 [0.81, 0.89]; n=1520 | 0.73 [0.66, 0.78]; n=1520 | —; n=1 |
| Sol | 0.90 [0.87, 0.93]; n=1516 | 0.99 [0.97, 1.00]; n=1500 | 0.77 [0.73, 0.82]; n=1516 | 0.70 [0.64, 0.76]; n=1516 | —; n=1 |
| Sonnet | 0.85 [0.81, 0.89]; n=1520 | 0.77 [0.73, 0.82]; n=1516 | 0.87 [0.82, 0.91]; n=1500 | 0.70 [0.64, 0.76]; n=1526 | —; n=1 |
| Luna | 0.73 [0.66, 0.78]; n=1520 | 0.70 [0.64, 0.76]; n=1516 | 0.70 [0.64, 0.76]; n=1526 | 0.73 [0.67, 0.78]; n=1500 | —; n=1 |
| DeepSeek | —; n=1 | —; n=1 | —; n=1 | —; n=1 | — |

## duplicates-mathlib-inclusive

[Library breakdowns](runs/main/duplicates-mathlib-inclusive/audit-comparison.md)

Opus uses the earlier prompt on four libraries, without Mathlib targets.

### Library comparison

| Library | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Mathlib | — | 689/1000<br>68.9% [66.0%, 71.7%] | 263/1000<br>26.3% [23.7%, 29.1%] | 596/1000<br>59.6% [56.5%, 62.6%] | — |
| Tau Ceti | 50/1000<br>5.0% [3.8%, 6.5%] | 142/1000<br>14.2% [12.2%, 16.5%] | 35/1000<br>3.5% [2.5%, 4.8%] | 150/1000<br>15.0% [12.9%, 17.3%] | — |
| Formal Frontier | 46/1000<br>4.6% [3.5%, 6.1%] | 212/1000<br>21.2% [18.8%, 23.8%] | 45/1000<br>4.5% [3.4%, 6.0%] | 229/1000<br>22.9% [20.4%, 25.6%] | — |
| Lean Pool | 68/1000<br>6.8% [5.4%, 8.5%] | 149/1000<br>14.9% [12.8%, 17.2%] | 58/1000<br>5.8% [4.5%, 7.4%] | 147/1000<br>14.7% [12.6%, 17.0%] | — |
| FLT (Anthropic) | 137/1000<br>13.7% [11.7%, 16.0%] | 255/1000<br>25.5% [22.9%, 28.3%] | 118/1000<br>11.8% [9.9%, 13.9%] | 230/1000<br>23.0% [20.5%, 25.7%] | — |
| OpenAI Math | 1/20<br>5.0% [0.9%, 23.6%] | 1/16<br>6.2% [1.1%, 28.3%] | 2/29<br>6.9% [1.9%, 22.0%] | 1/26<br>3.8% [0.7%, 18.9%] | — |

### Model comparison

Full-pass reference: **5000 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 4100 | 0/1 | 4020/4100 | 302 | 302 | 7.5% [6.7%, 8.4%] | $217.66 / $270.72 |
| Sol | 5100 | 0/1 | 5016/5100 | 1448 | 1448 | 28.9% [27.6%, 30.1%] | $320.53 / $319.51 |
| Sonnet | 5100 | 0/1 | 5029/5100 | 521 | 521 | 10.4% [9.5%, 11.2%] | $125.94 / $125.21 |
| Luna | 5100 | 0/1 | 5026/5100 | 1353 | 1353 | 26.9% [25.7%, 28.2%] | $16.08 / $16.00 |
| DeepSeek | 600 | 0/1 | 0/600 | 0 | 0 | — | $0.00 / — |

#### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | 0.57 [0.54, 0.60]; n=4016 | 0.74 [0.70, 0.78]; n=4020 | 0.54 [0.51, 0.58]; n=4020 | — |
| Sol | 0.57 [0.54, 0.60]; n=4016 | — | 0.48 [0.46, 0.51]; n=5016 | 0.69 [0.67, 0.72]; n=5016 | — |
| Sonnet | 0.74 [0.70, 0.78]; n=4020 | 0.48 [0.46, 0.51]; n=5016 | — | 0.50 [0.48, 0.53]; n=5026 | — |
| Luna | 0.54 [0.51, 0.58]; n=4020 | 0.69 [0.67, 0.72]; n=5016 | 0.50 [0.48, 0.53]; n=5026 | — | — |
| DeepSeek | — | — | — | — | — |

## concept-reinvention

[Library breakdowns](runs/file-quality-pilot-2026-10-21/reports/concept-reinvention-comparison.md)

### Library comparison

| Library | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Mathlib | — | — | 2/10<br>20.0% [5.7%, 51.0%] | 0/10<br>0.0% [0.0%, 27.8%] | — |
| Tau Ceti | — | — | 0/10<br>0.0% [0.0%, 27.8%] | 0/10<br>0.0% [0.0%, 27.8%] | — |
| Lean Pool | — | — | 4/10<br>40.0% [16.8%, 68.7%] | 0/10<br>0.0% [0.0%, 27.8%] | — |
| OpenAI Math | 2/20<br>10.0% [2.8%, 30.1%] | 1/16<br>6.2% [1.1%, 28.3%] | 3/29<br>10.3% [3.6%, 26.4%] | 3/26<br>11.5% [4.0%, 29.0%] | — |

### Model comparison

Full-pass reference: **30 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 100 | 0/1 | 20/100 | 2 | 2 | 10.0% [2.8%, 30.1%] | $2.85 / $4.28 |
| Sol | 100 | 0/1 | 16/100 | 1 | 1 | 6.2% [1.1%, 28.3%] | $1.50 / $2.81 |
| Sonnet | 130 | 0/1 | 59/130 | 9 | 9 | 15.3% [8.2%, 26.5%] | $4.49 / $2.28 |
| Luna | 130 | 0/1 | 56/130 | 3 | 3 | 5.4% [1.8%, 14.6%] | $0.29 / $0.16 |
| DeepSeek | 40 | 0/1 | 0/40 | 0 | 0 | — | $0.00 / — |

#### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | 0.68 [—]; n=16 | 1.00 [—]; n=20 | 0.69 [—]; n=20 | — |
| Sol | 0.68 [—]; n=16 | — | 0.68 [—]; n=16 | 1.00 [—]; n=16 | — |
| Sonnet | 1.00 [—]; n=20 | 0.68 [—]; n=16 | — | 0.11 [—]; n=56 | — |
| Luna | 0.69 [—]; n=20 | 1.00 [—]; n=16 | 0.11 [—]; n=56 | — | — |
| DeepSeek | — | — | — | — | — |

Coverage annotations: Opus: 0 partial, 9 not applicable; Sol: 0 partial, 3 not applicable; Sonnet: 0 partial, 14 not applicable; Luna: 0 partial, 0 not applicable; DeepSeek: 0 partial, 0 not applicable.

## statement-generality

[Library breakdowns](runs/file-quality-pilot-2026-10-21/reports/statement-generality-comparison.md)

### Library comparison

| Library | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Mathlib | — | — | 6/10<br>60.0% [31.3%, 83.2%] | 2/10<br>20.0% [5.7%, 51.0%] | — |
| Tau Ceti | — | — | 3/10<br>30.0% [10.8%, 60.3%] | 1/10<br>10.0% [1.8%, 40.4%] | — |
| Lean Pool | — | — | 9/10<br>90.0% [59.6%, 98.2%] | 8/10<br>80.0% [49.0%, 94.3%] | — |
| OpenAI Math | 13/19<br>68.4% [46.0%, 84.6%] | 13/16<br>81.2% [57.0%, 93.4%] | 22/29<br>75.9% [57.9%, 87.8%] | 12/26<br>46.2% [28.8%, 64.5%] | — |

### Model comparison

Full-pass reference: **30 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 100 | 0/1 | 19/100 | 13 | 13 | 68.4% [46.0%, 84.6%] | $6.75 / $10.66 |
| Sol | 100 | 0/1 | 16/100 | 13 | 13 | 81.2% [57.0%, 93.4%] | $2.26 / $4.23 |
| Sonnet | 130 | 0/1 | 59/130 | 40 | 40 | 67.8% [55.1%, 78.3%] | $6.91 / $3.51 |
| Luna | 130 | 0/1 | 56/130 | 23 | 23 | 41.1% [29.2%, 54.1%] | $0.27 / $0.14 |
| DeepSeek | 40 | 0/1 | 0/40 | 0 | 0 | — | $0.00 / — |

#### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | 0.37 [—]; n=16 | 0.62 [0.18, 1.00]; n=19 | 0.49 [0.07, 0.81]; n=19 | — |
| Sol | 0.37 [—]; n=16 | — | 0.83 [—]; n=16 | 0.48 [—]; n=16 | — |
| Sonnet | 0.62 [0.18, 1.00]; n=19 | 0.83 [—]; n=16 | — | 0.44 [0.25, 0.62]; n=56 | — |
| Luna | 0.49 [0.07, 0.81]; n=19 | 0.48 [—]; n=16 | 0.44 [0.25, 0.62]; n=56 | — | — |
| DeepSeek | — | — | — | — | — |

Coverage annotations: Opus: 0 partial, 1 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 1 not applicable; Luna: 0 partial, 0 not applicable; DeepSeek: 0 partial, 0 not applicable.

## vacuity-and-misstatement

[Library breakdowns](runs/file-quality-pilot-2026-10-21/reports/vacuity-and-misstatement-comparison.md)

### Library comparison

| Library | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Mathlib | — | — | 3/10<br>30.0% [10.8%, 60.3%] | 1/10<br>10.0% [1.8%, 40.4%] | — |
| Tau Ceti | — | — | 0/10<br>0.0% [0.0%, 27.8%] | 1/10<br>10.0% [1.8%, 40.4%] | — |
| Lean Pool | — | — | 2/10<br>20.0% [5.7%, 51.0%] | 0/10<br>0.0% [0.0%, 27.8%] | — |
| OpenAI Math | 0/19<br>0.0% [0.0%, 16.8%] | 0/15<br>0.0% [0.0%, 20.4%] | 0/29<br>0.0% [0.0%, 11.7%] | 1/26<br>3.8% [0.7%, 18.9%] | — |

### Model comparison

Full-pass reference: **30 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 100 | 0/1 | 19/100 | 0 | 0 | 0.0% [0.0%, 16.8%] | $4.28 / $6.76 |
| Sol | 100 | 0/1 | 15/100 | 0 | 0 | 0.0% [0.0%, 20.4%] | $1.35 / $2.69 |
| Sonnet | 130 | 0/1 | 59/130 | 5 | 5 | 8.5% [3.7%, 18.4%] | $5.11 / $2.60 |
| Luna | 130 | 0/1 | 56/130 | 3 | 3 | 5.4% [1.8%, 14.6%] | $0.26 / $0.14 |
| DeepSeek | 40 | 0/1 | 0/40 | 0 | 0 | — | $0.00 / — |

#### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | —; n=15 | —; n=19 | —; n=19 | — |
| Sol | —; n=15 | — | —; n=15 | —; n=15 | — |
| Sonnet | —; n=19 | —; n=15 | — | -0.07 [—]; n=56 | — |
| Luna | —; n=19 | —; n=15 | -0.07 [—]; n=56 | — | — |
| DeepSeek | — | — | — | — | — |

Coverage annotations: Opus: 0 partial, 1 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 0 not applicable; Luna: 0 partial, 0 not applicable; DeepSeek: 0 partial, 0 not applicable.

## simp-interface

[Library breakdowns](runs/file-quality-pilot-2026-10-21/reports/simp-interface-comparison.md)

### Library comparison

| Library | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Mathlib | — | — | 4/10<br>40.0% [16.8%, 68.7%] | 4/10<br>40.0% [16.8%, 68.7%] | — |
| Tau Ceti | — | — | 3/10<br>30.0% [10.8%, 60.3%] | 1/10<br>10.0% [1.8%, 40.4%] | — |
| Lean Pool | — | — | 6/10<br>60.0% [31.3%, 83.2%] | 6/10<br>60.0% [31.3%, 83.2%] | — |
| OpenAI Math | 11/19<br>57.9% [36.3%, 76.9%] | 4/15<br>26.7% [10.9%, 52.0%] | 15/28<br>53.6% [35.8%, 70.5%] | 8/25<br>32.0% [17.2%, 51.6%] | — |

### Model comparison

Full-pass reference: **30 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 100 | 0/1 | 19/100 | 11 | 11 | 57.9% [36.3%, 76.9%] | $5.49 / $8.66 |
| Sol | 100 | 0/1 | 15/100 | 4 | 4 | 26.7% [10.9%, 52.0%] | $1.51 / $3.03 |
| Sonnet | 130 | 0/1 | 58/130 | 28 | 28 | 48.3% [35.9%, 60.8%] | $5.12 / $2.65 |
| Luna | 130 | 0/1 | 55/130 | 19 | 19 | 34.5% [23.4%, 47.7%] | $0.26 / $0.14 |
| DeepSeek | 40 | 0/1 | 0/40 | 0 | 0 | — | $0.00 / — |

#### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | 0.49 [0.22, 0.76]; n=15 | 0.69 [0.32, 1.00]; n=19 | 0.43 [-0.02, 0.76]; n=19 | — |
| Sol | 0.49 [0.22, 0.76]; n=15 | — | 0.49 [0.24, 0.76]; n=15 | 0.53 [-0.10, 1.00]; n=15 | — |
| Sonnet | 0.69 [0.32, 1.00]; n=19 | 0.49 [0.24, 0.76]; n=15 | — | 0.36 [0.11, 0.59]; n=55 | — |
| Luna | 0.43 [-0.02, 0.76]; n=19 | 0.53 [-0.10, 1.00]; n=15 | 0.36 [0.11, 0.59]; n=55 | — | — |
| DeepSeek | — | — | — | — | — |

Coverage annotations: Opus: 0 partial, 2 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 3 not applicable; Luna: 0 partial, 0 not applicable; DeepSeek: 0 partial, 0 not applicable.

## repeated-proof-machinery

[Library breakdowns](runs/file-quality-pilot-2026-10-21/reports/repeated-proof-machinery-comparison.md)

### Library comparison

| Library | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Mathlib | — | — | 2/10<br>20.0% [5.7%, 51.0%] | 2/10<br>20.0% [5.7%, 51.0%] | — |
| Tau Ceti | — | — | 2/10<br>20.0% [5.7%, 51.0%] | 0/10<br>0.0% [0.0%, 27.8%] | — |
| Lean Pool | — | — | 6/10<br>60.0% [31.3%, 83.2%] | 3/10<br>30.0% [10.8%, 60.3%] | — |
| OpenAI Math | 6/19<br>31.6% [15.4%, 54.0%] | 2/15<br>13.3% [3.7%, 37.9%] | 11/28<br>39.3% [23.6%, 57.6%] | 5/25<br>20.0% [8.9%, 39.1%] | — |

### Model comparison

Full-pass reference: **30 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 100 | 0/1 | 19/100 | 6 | 6 | 31.6% [15.4%, 54.0%] | $4.42 / $6.98 |
| Sol | 100 | 0/1 | 15/100 | 2 | 2 | 13.3% [3.7%, 37.9%] | $1.27 / $2.54 |
| Sonnet | 130 | 0/1 | 58/130 | 21 | 21 | 36.2% [25.1%, 49.1%] | $4.35 / $2.25 |
| Luna | 130 | 0/1 | 55/130 | 10 | 10 | 18.2% [10.2%, 30.3%] | $0.20 / $0.11 |
| DeepSeek | 40 | 0/1 | 0/40 | 0 | 0 | — | $0.00 / — |

#### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | 0.48 [—]; n=15 | 0.62 [0.19, 1.00]; n=19 | 0.64 [—]; n=19 | — |
| Sol | 0.48 [—]; n=15 | — | 0.55 [—]; n=15 | 0.78 [—]; n=15 | — |
| Sonnet | 0.62 [0.19, 1.00]; n=19 | 0.55 [—]; n=15 | — | 0.55 [0.31, 0.75]; n=55 | — |
| Luna | 0.64 [—]; n=19 | 0.78 [—]; n=15 | 0.55 [0.31, 0.75]; n=55 | — | — |
| DeepSeek | — | — | — | — | — |

Coverage annotations: Opus: 0 partial, 1 not applicable; Sol: 0 partial, 1 not applicable; Sonnet: 0 partial, 2 not applicable; Luna: 0 partial, 0 not applicable; DeepSeek: 0 partial, 0 not applicable.

## readable-proof-simplification

[Library breakdowns](runs/file-quality-pilot-2026-10-21/reports/readable-proof-simplification-comparison.md)

### Library comparison

| Library | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Mathlib | — | — | 7/10<br>70.0% [39.7%, 89.2%] | 2/10<br>20.0% [5.7%, 51.0%] | — |
| Tau Ceti | — | — | 8/10<br>80.0% [49.0%, 94.3%] | 3/10<br>30.0% [10.8%, 60.3%] | — |
| Lean Pool | — | — | 9/10<br>90.0% [59.6%, 98.2%] | 6/10<br>60.0% [31.3%, 83.2%] | — |
| OpenAI Math | 15/19<br>78.9% [56.7%, 91.5%] | 8/14<br>57.1% [32.6%, 78.6%] | 22/28<br>78.6% [60.5%, 89.8%] | 5/25<br>20.0% [8.9%, 39.1%] | — |

### Model comparison

Full-pass reference: **30 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 100 | 0/1 | 19/100 | 15 | 15 | 78.9% [56.7%, 91.5%] | $6.06 / $9.56 |
| Sol | 100 | 0/1 | 14/100 | 8 | 8 | 57.1% [32.6%, 78.6%] | $1.68 / $3.61 |
| Sonnet | 130 | 0/1 | 58/130 | 46 | 46 | 79.3% [67.2%, 87.7%] | $7.41 / $3.83 |
| Luna | 130 | 0/1 | 55/130 | 16 | 16 | 29.1% [18.8%, 42.1%] | $0.21 / $0.12 |
| DeepSeek | 40 | 0/1 | 0/40 | 0 | 0 | — | $0.00 / — |

#### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | 0.41 [-0.17, 0.85]; n=14 | 0.57 [-0.02, 1.00]; n=19 | 0.27 [—]; n=19 | — |
| Sol | 0.41 [-0.17, 0.85]; n=14 | — | 0.41 [-0.18, 0.86]; n=14 | 0.10 [-0.45, 0.55]; n=14 | — |
| Sonnet | 0.57 [-0.02, 1.00]; n=19 | 0.41 [-0.18, 0.86]; n=14 | — | 0.34 [0.23, 0.46]; n=55 | — |
| Luna | 0.27 [—]; n=19 | 0.10 [-0.45, 0.55]; n=14 | 0.34 [0.23, 0.46]; n=55 | — | — |
| DeepSeek | — | — | — | — | — |

Coverage annotations: Opus: 0 partial, 1 not applicable; Sol: 0 partial, 1 not applicable; Sonnet: 0 partial, 1 not applicable; Luna: 0 partial, 1 not applicable; DeepSeek: 0 partial, 0 not applicable.
