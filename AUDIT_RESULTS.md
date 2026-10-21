# Audit results

Generated 2026-10-21T06:58:56+00:00 · [Methods and notation](AUDIT_METHODS.md) · [Cost summary](runs/main/api-equivalent-costs.md).

## Combined summary

Union across **8 audits**: a target counts once per model if any audit flags it. First passes only; theorem and file samples are counted separately. Each rate uses only targets reviewed on **every contributing audit**; a dash means no such targets. [Aggregation details](AUDIT_METHODS.md#combined-summary).

### Theorem audits: library comparison

Contributing audits: [unnecessary-hypotheses](#unnecessary-hypotheses), [duplicates-mathlib-inclusive](#duplicates-mathlib-inclusive).

| Library | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Mathlib | — | 215/300<br>71.7% [66.3%, 76.5%] | 85/300<br>28.3% [23.5%, 33.7%] | 176/300<br>58.7% [53.0%, 64.1%] |
| Tau Ceti | 39/400<br>9.8% [7.2%, 13.1%] | 65/300<br>21.7% [17.4%, 26.7%] | 22/300<br>7.3% [4.9%, 10.9%] | 62/300<br>20.7% [16.5%, 25.6%] |
| Formal Frontier | 32/400<br>8.0% [5.7%, 11.1%] | 78/300<br>26.0% [21.4%, 31.2%] | 19/300<br>6.3% [4.1%, 9.7%] | 78/300<br>26.0% [21.4%, 31.2%] |
| Lean Pool | 83/400<br>20.8% [17.1%, 25.0%] | 95/300<br>31.7% [26.7%, 37.1%] | 55/300<br>18.3% [14.4%, 23.1%] | 87/300<br>29.0% [24.2%, 34.4%] |
| FLT (Anthropic) | 123/400<br>30.8% [26.4%, 35.4%] | 148/300<br>49.3% [43.7%, 55.0%] | 75/300<br>25.0% [20.4%, 30.2%] | 118/300<br>39.3% [34.0%, 45.0%] |
| OpenAI Math | 2/15<br>13.3% [3.7%, 37.9%] | 3/10<br>30.0% [10.8%, 60.3%] | 2/22<br>9.1% [2.5%, 27.8%] | 3/20<br>15.0% [5.2%, 36.0%] |

### File audits: library comparison

Contributing audits: [concept-reinvention](#concept-reinvention), [statement-generality](#statement-generality), [vacuity-and-misstatement](#vacuity-and-misstatement), [simp-interface](#simp-interface), [repeated-proof-machinery](#repeated-proof-machinery), [readable-proof-simplification](#readable-proof-simplification).

| Library | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Mathlib | — | — | 10/10<br>100.0% [72.2%, 100.0%] | 8/10<br>80.0% [49.0%, 94.3%] |
| Tau Ceti | — | — | 9/10<br>90.0% [59.6%, 98.2%] | 4/10<br>40.0% [16.8%, 68.7%] |
| Lean Pool | — | — | 9/10<br>90.0% [59.6%, 98.2%] | 8/10<br>80.0% [49.0%, 94.3%] |
| OpenAI Math | 12/14<br>85.7% [60.1%, 96.0%] | 8/9<br>88.9% [56.5%, 98.0%] | 18/21<br>85.7% [65.4%, 95.0%] | 13/19<br>68.4% [46.0%, 84.6%] |

### Model comparison

| Model | Audits with results | Theorems selected | Files selected | Audit passes done/planned | Theorems flagged / reviewed | Files flagged / reviewed | Judgments done/planned | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| Opus | 8/8 | 4500 | 100 | 1/9 | 279/1615 | 12/14 | 7615/8300 | $494.29 / $461.67 |
| Sol | 8/8 | 5100 | 100 | 1/9 | 604/1510 | 8/9 | 8075/8800 | $467.31 / $433.13 |
| Sonnet | 8/8 | 5100 | 130 | 1/9 | 258/1522 | 46/51 | 8355/8980 | $260.84 / $212.20 |
| Luna | 8/8 | 5100 | 130 | 1/9 | 524/1520 | 33/49 | 8339/8980 | $23.96 / $21.15 |

### Theorem union correlations

| Model | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Opus | 0.92 [0.89, 0.95]; n=1500 | 0.67 [0.63, 0.71]; n=1210 | 0.80 [0.76, 0.84]; n=1215 | 0.55 [0.50, 0.60]; n=1215 |
| Sol | 0.67 [0.63, 0.71]; n=1210 | 0.99 [0.97, 1.00]; n=1500 | 0.53 [0.50, 0.56]; n=1510 | 0.65 [0.61, 0.69]; n=1510 |
| Sonnet | 0.80 [0.76, 0.84]; n=1215 | 0.53 [0.50, 0.56]; n=1510 | 0.87 [0.83, 0.92]; n=1500 | 0.51 [0.46, 0.55]; n=1520 |
| Luna | 0.55 [0.50, 0.60]; n=1215 | 0.65 [0.61, 0.69]; n=1510 | 0.51 [0.46, 0.55]; n=1520 | 0.73 [0.66, 0.78]; n=1500 |

### File union correlations

| Model | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Opus | — | 1.00 [—]; n=9 | 1.00 [—]; n=14 | 0.65 [—]; n=14 |
| Sol | 1.00 [—]; n=9 | — | 1.00 [—]; n=9 | 0.50 [—]; n=9 |
| Sonnet | 1.00 [—]; n=14 | 1.00 [—]; n=9 | — | 0.48 [0.25, 0.68]; n=49 |
| Luna | 0.65 [—]; n=14 | 0.50 [—]; n=9 | 0.48 [0.25, 0.68]; n=49 | — |

## unnecessary-hypotheses

[Library breakdowns](runs/main/unnecessary-hypotheses/audit-comparison.md)

### Library comparison

| Library | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Mathlib | 15/400<br>3.8% [2.3%, 6.1%] | 12/300<br>4.0% [2.3%, 6.9%] | 6/300<br>2.0% [0.9%, 4.3%] | 12/300<br>4.0% [2.3%, 6.9%] |
| Tau Ceti | 23/400<br>5.8% [3.9%, 8.5%] | 19/300<br>6.3% [4.1%, 9.7%] | 12/300<br>4.0% [2.3%, 6.9%] | 19/300<br>6.3% [4.1%, 9.7%] |
| Formal Frontier | 17/400<br>4.2% [2.7%, 6.7%] | 18/300<br>6.0% [3.8%, 9.3%] | 12/300<br>4.0% [2.3%, 6.9%] | 15/300<br>5.0% [3.1%, 8.1%] |
| Lean Pool | 61/400<br>15.2% [12.1%, 19.1%] | 60/300<br>20.0% [15.9%, 24.9%] | 39/300<br>13.0% [9.7%, 17.3%] | 48/300<br>16.0% [12.3%, 20.6%] |
| FLT (Anthropic) | 82/400<br>20.5% [16.8%, 24.7%] | 78/300<br>26.0% [21.4%, 31.2%] | 52/300<br>17.3% [13.5%, 22.0%] | 61/300<br>20.3% [16.2%, 25.2%] |
| OpenAI Math | 1/15<br>6.7% [1.2%, 29.8%] | 2/11<br>18.2% [5.1%, 47.7%] | 1/22<br>4.5% [0.8%, 21.8%] | 2/20<br>10.0% [2.8%, 30.1%] |

### Model comparison

Full-pass reference: **2000 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 2100 | 1/2 | 3515/3600 | 349 | 206 | 9.9% [8.6%, 11.3%] | $255.50 / $145.38 |
| Sol | 1600 | 1/2 | 3011/3100 | 376 | 191 | 12.5% [10.9%, 14.3%] | $141.24 / $93.81 |
| Sonnet | 1600 | 1/2 | 3022/3100 | 246 | 138 | 8.0% [6.8%, 9.5%] | $106.33 / $70.37 |
| Luna | 1600 | 1/2 | 3020/3100 | 312 | 195 | 10.3% [8.9%, 12.0%] | $6.55 / $4.34 |

#### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Opus | 0.92 [0.89, 0.95]; n=1500 | 0.90 [0.87, 0.93]; n=1511 | 0.85 [0.80, 0.89]; n=1515 | 0.73 [0.67, 0.78]; n=1515 |
| Sol | 0.90 [0.87, 0.93]; n=1511 | 0.99 [0.97, 1.00]; n=1500 | 0.77 [0.72, 0.82]; n=1511 | 0.70 [0.64, 0.76]; n=1511 |
| Sonnet | 0.85 [0.80, 0.89]; n=1515 | 0.77 [0.72, 0.82]; n=1511 | 0.87 [0.82, 0.91]; n=1500 | 0.70 [0.64, 0.76]; n=1520 |
| Luna | 0.73 [0.67, 0.78]; n=1515 | 0.70 [0.64, 0.76]; n=1511 | 0.70 [0.64, 0.76]; n=1520 | 0.73 [0.67, 0.78]; n=1500 |

## duplicates-mathlib-inclusive

[Library breakdowns](runs/main/duplicates-mathlib-inclusive/audit-comparison.md)

Opus uses the earlier prompt on four libraries, without Mathlib targets.

### Library comparison

| Library | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Mathlib | — | 689/1000<br>68.9% [66.0%, 71.7%] | 263/1000<br>26.3% [23.7%, 29.1%] | 596/1000<br>59.6% [56.5%, 62.6%] |
| Tau Ceti | 50/1000<br>5.0% [3.8%, 6.5%] | 142/1000<br>14.2% [12.2%, 16.5%] | 35/1000<br>3.5% [2.5%, 4.8%] | 150/1000<br>15.0% [12.9%, 17.3%] |
| Formal Frontier | 46/1000<br>4.6% [3.5%, 6.1%] | 212/1000<br>21.2% [18.8%, 23.8%] | 45/1000<br>4.5% [3.4%, 6.0%] | 229/1000<br>22.9% [20.4%, 25.6%] |
| Lean Pool | 68/1000<br>6.8% [5.4%, 8.5%] | 149/1000<br>14.9% [12.8%, 17.2%] | 58/1000<br>5.8% [4.5%, 7.4%] | 147/1000<br>14.7% [12.6%, 17.0%] |
| FLT (Anthropic) | 137/1000<br>13.7% [11.7%, 16.0%] | 255/1000<br>25.5% [22.9%, 28.3%] | 118/1000<br>11.8% [9.9%, 13.9%] | 230/1000<br>23.0% [20.5%, 25.7%] |
| OpenAI Math | 1/15<br>6.7% [1.2%, 29.8%] | 1/10<br>10.0% [1.8%, 40.4%] | 1/22<br>4.5% [0.8%, 21.8%] | 1/20<br>5.0% [0.9%, 23.6%] |

### Model comparison

Full-pass reference: **5000 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 4100 | 0/1 | 4015/4100 | 302 | 302 | 7.5% [6.7%, 8.4%] | $217.36 / $270.68 |
| Sol | 5100 | 0/1 | 5010/5100 | 1448 | 1448 | 28.9% [27.7%, 30.2%] | $320.12 / $319.48 |
| Sonnet | 5100 | 0/1 | 5022/5100 | 520 | 520 | 10.4% [9.5%, 11.2%] | $125.69 / $125.13 |
| Luna | 5100 | 0/1 | 5020/5100 | 1353 | 1353 | 27.0% [25.7%, 28.2%] | $16.07 / $16.00 |

#### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Opus | — | 0.57 [0.54, 0.60]; n=4010 | 0.74 [0.70, 0.78]; n=4015 | 0.54 [0.51, 0.58]; n=4015 |
| Sol | 0.57 [0.54, 0.60]; n=4010 | — | 0.48 [0.46, 0.51]; n=5010 | 0.69 [0.67, 0.71]; n=5010 |
| Sonnet | 0.74 [0.70, 0.78]; n=4015 | 0.48 [0.46, 0.51]; n=5010 | — | 0.50 [0.48, 0.53]; n=5020 |
| Luna | 0.54 [0.51, 0.58]; n=4015 | 0.69 [0.67, 0.71]; n=5010 | 0.50 [0.48, 0.53]; n=5020 | — |

## concept-reinvention

[Library breakdowns](runs/file-quality-pilot-2026-10-21/reports/concept-reinvention-comparison.md)

### Library comparison

| Library | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Mathlib | — | — | 2/10<br>20.0% [5.7%, 51.0%] | 0/10<br>0.0% [0.0%, 27.8%] |
| Tau Ceti | — | — | 0/10<br>0.0% [0.0%, 27.8%] | 0/10<br>0.0% [0.0%, 27.8%] |
| Lean Pool | — | — | 4/10<br>40.0% [16.8%, 68.7%] | 0/10<br>0.0% [0.0%, 27.8%] |
| OpenAI Math | 2/15<br>13.3% [3.7%, 37.9%] | 1/9<br>11.1% [2.0%, 43.5%] | 3/22<br>13.6% [4.7%, 33.3%] | 1/20<br>5.0% [0.9%, 23.6%] |

### Model comparison

Full-pass reference: **30 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 100 | 0/1 | 15/100 | 2 | 2 | 13.3% [3.7%, 37.9%] | $2.19 / $4.37 |
| Sol | 100 | 0/1 | 9/100 | 1 | 1 | 11.1% [2.0%, 43.5%] | $0.80 / $2.65 |
| Sonnet | 130 | 0/1 | 52/130 | 9 | 9 | 17.3% [9.4%, 29.7%] | $3.90 / $2.25 |
| Luna | 130 | 0/1 | 50/130 | 1 | 1 | 2.0% [0.4%, 10.5%] | $0.26 / $0.15 |

#### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Opus | — | 1.00 [—]; n=9 | 1.00 [—]; n=15 | 0.68 [—]; n=15 |
| Sol | 1.00 [—]; n=9 | — | 1.00 [—]; n=9 | 1.00 [—]; n=9 |
| Sonnet | 1.00 [—]; n=15 | 1.00 [—]; n=9 | — | 0.33 [—]; n=50 |
| Luna | 0.68 [—]; n=15 | 1.00 [—]; n=9 | 0.33 [—]; n=50 | — |

Coverage annotations: Opus: 0 partial, 7 not applicable; Sol: 0 partial, 3 not applicable; Sonnet: 0 partial, 12 not applicable; Luna: 0 partial, 0 not applicable.

## statement-generality

[Library breakdowns](runs/file-quality-pilot-2026-10-21/reports/statement-generality-comparison.md)

### Library comparison

| Library | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Mathlib | — | — | 6/10<br>60.0% [31.3%, 83.2%] | 2/10<br>20.0% [5.7%, 51.0%] |
| Tau Ceti | — | — | 3/10<br>30.0% [10.8%, 60.3%] | 1/10<br>10.0% [1.8%, 40.4%] |
| Lean Pool | — | — | 9/10<br>90.0% [59.6%, 98.2%] | 8/10<br>80.0% [49.0%, 94.3%] |
| OpenAI Math | 10/14<br>71.4% [45.4%, 88.3%] | 8/9<br>88.9% [56.5%, 98.0%] | 16/22<br>72.7% [51.8%, 86.8%] | 10/20<br>50.0% [29.9%, 70.1%] |

### Model comparison

Full-pass reference: **30 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 100 | 0/1 | 14/100 | 10 | 10 | 71.4% [45.4%, 88.3%] | $4.72 / $10.12 |
| Sol | 100 | 0/1 | 9/100 | 8 | 8 | 88.9% [56.5%, 98.0%] | $1.32 / $4.38 |
| Sonnet | 130 | 0/1 | 52/130 | 34 | 34 | 65.4% [51.8%, 76.8%] | $5.93 / $3.42 |
| Luna | 130 | 0/1 | 50/130 | 21 | 21 | 42.0% [29.4%, 55.8%] | $0.24 / $0.14 |

#### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Opus | — | 0.50 [—]; n=9 | 0.65 [0.15, 1.00]; n=14 | 0.41 [-0.17, 0.86]; n=14 |
| Sol | 0.50 [—]; n=9 | — | 0.66 [—]; n=9 | 0.50 [—]; n=9 |
| Sonnet | 0.65 [0.15, 1.00]; n=14 | 0.66 [—]; n=9 | — | 0.47 [0.25, 0.66]; n=50 |
| Luna | 0.41 [-0.17, 0.86]; n=14 | 0.50 [—]; n=9 | 0.47 [0.25, 0.66]; n=50 | — |

Coverage annotations: Opus: 0 partial, 1 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 1 not applicable; Luna: 0 partial, 0 not applicable.

## vacuity-and-misstatement

[Library breakdowns](runs/file-quality-pilot-2026-10-21/reports/vacuity-and-misstatement-comparison.md)

### Library comparison

| Library | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Mathlib | — | — | 3/10<br>30.0% [10.8%, 60.3%] | 1/10<br>10.0% [1.8%, 40.4%] |
| Tau Ceti | — | — | 0/10<br>0.0% [0.0%, 27.8%] | 1/10<br>10.0% [1.8%, 40.4%] |
| Lean Pool | — | — | 2/10<br>20.0% [5.7%, 51.0%] | 0/10<br>0.0% [0.0%, 27.8%] |
| OpenAI Math | 0/14<br>0.0% [0.0%, 21.5%] | 0/9<br>0.0% [0.0%, 29.9%] | 0/22<br>0.0% [0.0%, 14.9%] | 0/20<br>0.0% [0.0%, 16.1%] |

### Model comparison

Full-pass reference: **30 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 100 | 0/1 | 14/100 | 0 | 0 | 0.0% [0.0%, 21.5%] | $2.75 / $5.89 |
| Sol | 100 | 0/1 | 9/100 | 0 | 0 | 0.0% [0.0%, 29.9%] | $0.86 / $2.86 |
| Sonnet | 130 | 0/1 | 52/130 | 5 | 5 | 9.6% [4.2%, 20.6%] | $4.55 / $2.63 |
| Luna | 130 | 0/1 | 50/130 | 2 | 2 | 4.0% [1.1%, 13.5%] | $0.23 / $0.14 |

#### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Opus | — | —; n=9 | —; n=14 | —; n=14 |
| Sol | —; n=9 | — | —; n=9 | —; n=9 |
| Sonnet | —; n=14 | —; n=9 | — | -0.07 [—]; n=50 |
| Luna | —; n=14 | —; n=9 | -0.07 [—]; n=50 | — |

Coverage annotations: Opus: 0 partial, 1 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 0 not applicable; Luna: 0 partial, 0 not applicable.

## simp-interface

[Library breakdowns](runs/file-quality-pilot-2026-10-21/reports/simp-interface-comparison.md)

### Library comparison

| Library | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Mathlib | — | — | 4/10<br>40.0% [16.8%, 68.7%] | 4/10<br>40.0% [16.8%, 68.7%] |
| Tau Ceti | — | — | 3/10<br>30.0% [10.8%, 60.3%] | 1/10<br>10.0% [1.8%, 40.4%] |
| Lean Pool | — | — | 6/10<br>60.0% [31.3%, 83.2%] | 6/10<br>60.0% [31.3%, 83.2%] |
| OpenAI Math | 8/14<br>57.1% [32.6%, 78.6%] | 2/9<br>22.2% [6.3%, 54.7%] | 12/22<br>54.5% [34.7%, 73.1%] | 7/20<br>35.0% [18.1%, 56.7%] |

### Model comparison

Full-pass reference: **30 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 100 | 0/1 | 14/100 | 8 | 8 | 57.1% [32.6%, 78.6%] | $3.74 / $8.01 |
| Sol | 100 | 0/1 | 9/100 | 2 | 2 | 22.2% [6.3%, 54.7%] | $0.96 / $3.21 |
| Sonnet | 130 | 0/1 | 52/130 | 25 | 25 | 48.1% [35.1%, 61.3%] | $4.51 / $2.60 |
| Luna | 130 | 0/1 | 50/130 | 18 | 18 | 36.0% [24.1%, 49.9%] | $0.24 / $0.14 |

#### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Opus | — | 0.38 [—]; n=9 | 0.71 [0.26, 1.00]; n=14 | 0.65 [0.35, 1.00]; n=14 |
| Sol | 0.38 [—]; n=9 | — | 0.38 [—]; n=9 | 0.19 [—]; n=9 |
| Sonnet | 0.71 [0.26, 1.00]; n=14 | 0.38 [—]; n=9 | — | 0.39 [0.14, 0.63]; n=50 |
| Luna | 0.65 [0.35, 1.00]; n=14 | 0.19 [—]; n=9 | 0.39 [0.14, 0.63]; n=50 | — |

Coverage annotations: Opus: 0 partial, 1 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 3 not applicable; Luna: 0 partial, 0 not applicable.

## repeated-proof-machinery

[Library breakdowns](runs/file-quality-pilot-2026-10-21/reports/repeated-proof-machinery-comparison.md)

### Library comparison

| Library | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Mathlib | — | — | 2/10<br>20.0% [5.7%, 51.0%] | 2/10<br>20.0% [5.7%, 51.0%] |
| Tau Ceti | — | — | 2/10<br>20.0% [5.7%, 51.0%] | 0/10<br>0.0% [0.0%, 27.8%] |
| Lean Pool | — | — | 6/10<br>60.0% [31.3%, 83.2%] | 3/10<br>30.0% [10.8%, 60.3%] |
| OpenAI Math | 6/14<br>42.9% [21.4%, 67.4%] | 1/9<br>11.1% [2.0%, 43.5%] | 7/22<br>31.8% [16.4%, 52.7%] | 3/20<br>15.0% [5.2%, 36.0%] |

### Model comparison

Full-pass reference: **30 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 100 | 0/1 | 14/100 | 6 | 6 | 42.9% [21.4%, 67.4%] | $3.67 / $7.87 |
| Sol | 100 | 0/1 | 9/100 | 1 | 1 | 11.1% [2.0%, 43.5%] | $0.86 / $2.87 |
| Sonnet | 130 | 0/1 | 52/130 | 17 | 17 | 32.7% [21.5%, 46.2%] | $3.73 / $2.15 |
| Luna | 130 | 0/1 | 50/130 | 8 | 8 | 16.0% [8.3%, 28.5%] | $0.18 / $0.11 |

#### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Opus | — | 0.32 [—]; n=9 | 0.56 [0.06, 1.00]; n=14 | 0.60 [—]; n=14 |
| Sol | 0.32 [—]; n=9 | — | 0.50 [—]; n=9 | 0.66 [—]; n=9 |
| Sonnet | 0.56 [0.06, 1.00]; n=14 | 0.50 [—]; n=9 | — | 0.55 [0.29, 0.77]; n=50 |
| Luna | 0.60 [—]; n=14 | 0.66 [—]; n=9 | 0.55 [0.29, 0.77]; n=50 | — |

Coverage annotations: Opus: 0 partial, 1 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 2 not applicable; Luna: 0 partial, 0 not applicable.

## readable-proof-simplification

[Library breakdowns](runs/file-quality-pilot-2026-10-21/reports/readable-proof-simplification-comparison.md)

### Library comparison

| Library | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Mathlib | — | — | 7/10<br>70.0% [39.7%, 89.2%] | 2/10<br>20.0% [5.7%, 51.0%] |
| Tau Ceti | — | — | 8/10<br>80.0% [49.0%, 94.3%] | 3/10<br>30.0% [10.8%, 60.3%] |
| Lean Pool | — | — | 9/10<br>90.0% [59.6%, 98.2%] | 6/10<br>60.0% [31.3%, 83.2%] |
| OpenAI Math | 11/14<br>78.6% [52.4%, 92.4%] | 6/9<br>66.7% [35.4%, 87.9%] | 16/21<br>76.2% [54.9%, 89.4%] | 4/19<br>21.1% [8.5%, 43.3%] |

### Model comparison

Full-pass reference: **30 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 100 | 0/1 | 14/100 | 11 | 11 | 78.6% [52.4%, 92.4%] | $4.36 / $9.34 |
| Sol | 100 | 0/1 | 9/100 | 6 | 6 | 66.7% [35.4%, 87.9%] | $1.16 / $3.85 |
| Sonnet | 130 | 0/1 | 51/130 | 40 | 40 | 78.4% [65.4%, 87.5%] | $6.20 / $3.65 |
| Luna | 130 | 0/1 | 49/130 | 15 | 15 | 30.6% [19.5%, 44.5%] | $0.20 / $0.12 |

#### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Opus | — | 0.19 [—]; n=9 | 0.83 [—]; n=14 | 0.27 [—]; n=14 |
| Sol | 0.19 [—]; n=9 | — | 0.50 [—]; n=9 | 0.38 [—]; n=9 |
| Sonnet | 0.83 [—]; n=14 | 0.50 [—]; n=9 | — | 0.36 [0.22, 0.48]; n=49 |
| Luna | 0.27 [—]; n=14 | 0.38 [—]; n=9 | 0.36 [0.22, 0.48]; n=49 | — |

Coverage annotations: Opus: 0 partial, 1 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 1 not applicable; Luna: 0 partial, 1 not applicable.
