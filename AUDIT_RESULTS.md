# Audit results

Generated 2026-10-21T11:05:06+00:00 · [Methods and notation](AUDIT_METHODS.md) · [Cost summary](runs/main/api-equivalent-costs.md).

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
| OpenAI Math | 3/22<br>13.6% [4.7%, 33.3%] | 16/70<br>22.9% [14.6%, 34.0%] | 8/41<br>19.5% [10.2%, 34.0%] | 12/48<br>25.0% [14.9%, 38.8%] | — |

### File audits: library comparison

Contributing audits: [concept-reinvention](#concept-reinvention), [statement-generality](#statement-generality), [vacuity-and-misstatement](#vacuity-and-misstatement), [simp-interface](#simp-interface), [repeated-proof-machinery](#repeated-proof-machinery), [readable-proof-simplification](#readable-proof-simplification).

| Library | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Mathlib | — | — | 10/10<br>100.0% [72.2%, 100.0%] | 8/10<br>80.0% [49.0%, 94.3%] | — |
| Tau Ceti | — | — | 9/10<br>90.0% [59.6%, 98.2%] | 4/10<br>40.0% [16.8%, 68.7%] | — |
| Lean Pool | — | — | 9/10<br>90.0% [59.6%, 98.2%] | 8/10<br>80.0% [49.0%, 94.3%] | — |
| OpenAI Math | 20/22<br>90.9% [72.2%, 97.5%] | 63/68<br>92.6% [83.9%, 96.8%] | 37/40<br>92.5% [80.1%, 97.4%] | 34/47<br>72.3% [58.2%, 83.1%] | — |

### Model comparison

| Model | Audits with results | Theorems selected | Files selected | Audit passes done/planned | Theorems flagged / reviewed | Files flagged / reviewed | Judgments done/planned | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| Opus | 8/8 | 4500 | 100 | 1/9 | 280/1622 | 20/22 | 7676/8300 | $509.85 / $464.84 |
| Sol | 8/8 | 5100 | 100 | 1/9 | 617/1570 | 63/68 | 8557/8800 | $512.12 / $432.46 |
| Sonnet | 8/8 | 5100 | 130 | 1/9 | 264/1541 | 65/70 | 8502/8980 | $273.74 / $213.07 |
| Luna | 8/8 | 5100 | 130 | 1/9 | 533/1548 | 54/77 | 8560/8980 | $24.86 / $21.16 |
| DeepSeek | 1/8 | 600 | 40 | 0/8 | — | — | 1/1440 | $0.01 / — |

### Theorem union correlations

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | 0.92 [0.89, 0.95]; n=1500 | 0.67 [0.64, 0.71]; n=1222 | 0.80 [0.75, 0.84]; n=1222 | 0.55 [0.50, 0.60]; n=1222 | —; n=1 |
| Sol | 0.67 [0.64, 0.71]; n=1222 | 0.99 [0.97, 1.00]; n=1500 | 0.53 [0.50, 0.57]; n=1541 | 0.66 [0.62, 0.70]; n=1548 | —; n=1 |
| Sonnet | 0.80 [0.75, 0.84]; n=1222 | 0.53 [0.50, 0.57]; n=1541 | 0.87 [0.83, 0.92]; n=1500 | 0.51 [0.47, 0.55]; n=1541 | —; n=1 |
| Luna | 0.55 [0.50, 0.60]; n=1222 | 0.66 [0.62, 0.70]; n=1548 | 0.51 [0.47, 0.55]; n=1541 | 0.73 [0.66, 0.78]; n=1500 | —; n=1 |
| DeepSeek | —; n=1 | —; n=1 | —; n=1 | —; n=1 | — |

### File union correlations

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | 1.00 [—]; n=22 | 0.80 [—]; n=22 | 0.46 [—]; n=22 | — |
| Sol | 1.00 [—]; n=22 | — | 0.54 [—]; n=40 | 0.15 [-0.15, 0.46]; n=47 | — |
| Sonnet | 0.80 [—]; n=22 | 0.54 [—]; n=40 | — | 0.41 [0.23, 0.57]; n=70 | — |
| Luna | 0.46 [—]; n=22 | 0.15 [-0.15, 0.46]; n=47 | 0.41 [0.23, 0.57]; n=70 | — | — |
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
| OpenAI Math | 2/22<br>9.1% [2.5%, 27.8%] | 14/70<br>20.0% [12.3%, 30.8%] | 6/41<br>14.6% [6.9%, 28.4%] | 10/48<br>20.8% [11.7%, 34.3%] | — |

### Model comparison

Full-pass reference: **2000 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 2100 | 1/2 | 3522/3600 | 350 | 207 | 9.9% [8.7%, 11.3%] | $256.57 / $145.70 |
| Sol | 1600 | 1/2 | 3070/3100 | 388 | 203 | 12.8% [11.2%, 14.5%] | $144.28 / $94.00 |
| Sonnet | 1600 | 1/2 | 3041/3100 | 251 | 143 | 8.2% [7.0%, 9.7%] | $107.41 / $70.64 |
| Luna | 1600 | 1/2 | 3048/3100 | 320 | 203 | 10.7% [9.2%, 12.3%] | $6.64 / $4.36 |
| DeepSeek | 600 | 0/1 | 1/600 | 0 | 0 | 0.0% [0.0%, 79.3%] | $0.01 / $26.51 |

#### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | 0.92 [0.89, 0.95]; n=1500 | 0.90 [0.87, 0.93]; n=1522 | 0.85 [0.80, 0.89]; n=1522 | 0.73 [0.67, 0.78]; n=1522 | —; n=1 |
| Sol | 0.90 [0.87, 0.93]; n=1522 | 0.99 [0.97, 1.00]; n=1500 | 0.78 [0.73, 0.82]; n=1541 | 0.71 [0.66, 0.76]; n=1548 | —; n=1 |
| Sonnet | 0.85 [0.80, 0.89]; n=1522 | 0.78 [0.73, 0.82]; n=1541 | 0.87 [0.82, 0.91]; n=1500 | 0.71 [0.64, 0.77]; n=1541 | —; n=1 |
| Luna | 0.73 [0.67, 0.78]; n=1522 | 0.71 [0.66, 0.76]; n=1548 | 0.71 [0.64, 0.77]; n=1541 | 0.73 [0.67, 0.78]; n=1500 | —; n=1 |
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
| OpenAI Math | 1/22<br>4.5% [0.8%, 21.8%] | 2/70<br>2.9% [0.8%, 9.8%] | 2/41<br>4.9% [1.3%, 16.1%] | 2/48<br>4.2% [1.2%, 14.0%] | — |

### Model comparison

Full-pass reference: **5000 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 4100 | 0/1 | 4022/4100 | 302 | 302 | 7.5% [6.7%, 8.4%] | $217.81 / $270.77 |
| Sol | 5100 | 0/1 | 5070/5100 | 1449 | 1449 | 28.6% [27.4%, 29.8%] | $324.01 / $319.54 |
| Sonnet | 5100 | 0/1 | 5041/5100 | 521 | 521 | 10.3% [9.5%, 11.2%] | $126.30 / $125.28 |
| Luna | 5100 | 0/1 | 5048/5100 | 1354 | 1354 | 26.8% [25.6%, 28.1%] | $16.16 / $16.00 |
| DeepSeek | 600 | 0/1 | 0/600 | 0 | 0 | — | $0.00 / — |

#### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | 0.57 [0.54, 0.60]; n=4022 | 0.74 [0.70, 0.78]; n=4022 | 0.54 [0.51, 0.58]; n=4022 | — |
| Sol | 0.57 [0.54, 0.60]; n=4022 | — | 0.48 [0.46, 0.50]; n=5041 | 0.69 [0.67, 0.71]; n=5048 | — |
| Sonnet | 0.74 [0.70, 0.78]; n=4022 | 0.48 [0.46, 0.50]; n=5041 | — | 0.50 [0.48, 0.53]; n=5041 | — |
| Luna | 0.54 [0.51, 0.58]; n=4022 | 0.69 [0.67, 0.71]; n=5048 | 0.50 [0.48, 0.53]; n=5041 | — | — |
| DeepSeek | — | — | — | — | — |

## concept-reinvention

[Library breakdowns](runs/file-quality-pilot-2026-10-21/reports/concept-reinvention-comparison.md)

### Library comparison

| Library | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Mathlib | — | — | 2/10<br>20.0% [5.7%, 51.0%] | 0/10<br>0.0% [0.0%, 27.8%] | — |
| Tau Ceti | — | — | 0/10<br>0.0% [0.0%, 27.8%] | 0/10<br>0.0% [0.0%, 27.8%] | — |
| Lean Pool | — | — | 4/10<br>40.0% [16.8%, 68.7%] | 0/10<br>0.0% [0.0%, 27.8%] | — |
| OpenAI Math | 3/22<br>13.6% [4.7%, 33.3%] | 1/70<br>1.4% [0.3%, 7.7%] | 3/40<br>7.5% [2.6%, 19.9%] | 3/48<br>6.2% [2.1%, 16.8%] | — |

### Model comparison

Full-pass reference: **30 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 100 | 0/1 | 22/100 | 3 | 3 | 13.6% [4.7%, 33.3%] | $3.37 / $4.60 |
| Sol | 100 | 0/1 | 70/100 | 1 | 1 | 1.4% [0.3%, 7.7%] | $6.15 / $2.64 |
| Sonnet | 130 | 0/1 | 70/130 | 9 | 9 | 12.9% [6.9%, 22.7%] | $4.98 / $2.14 |
| Luna | 130 | 0/1 | 78/130 | 3 | 3 | 3.8% [1.3%, 10.7%] | $0.40 / $0.15 |
| DeepSeek | 40 | 0/1 | 0/40 | 0 | 0 | — | $0.00 / — |

#### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | 0.55 [—]; n=22 | 1.00 [—]; n=22 | 0.55 [—]; n=22 | — |
| Sol | 0.55 [—]; n=22 | — | 0.56 [—]; n=40 | 0.56 [—]; n=48 | — |
| Sonnet | 1.00 [—]; n=22 | 0.56 [—]; n=40 | — | 0.13 [—]; n=70 | — |
| Luna | 0.55 [—]; n=22 | 0.56 [—]; n=48 | 0.13 [—]; n=70 | — | — |
| DeepSeek | — | — | — | — | — |

Coverage annotations: Opus: 0 partial, 9 not applicable; Sol: 0 partial, 15 not applicable; Sonnet: 0 partial, 17 not applicable; Luna: 0 partial, 0 not applicable; DeepSeek: 0 partial, 0 not applicable.

## statement-generality

[Library breakdowns](runs/file-quality-pilot-2026-10-21/reports/statement-generality-comparison.md)

### Library comparison

| Library | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Mathlib | — | — | 6/10<br>60.0% [31.3%, 83.2%] | 2/10<br>20.0% [5.7%, 51.0%] | — |
| Tau Ceti | — | — | 3/10<br>30.0% [10.8%, 60.3%] | 1/10<br>10.0% [1.8%, 40.4%] | — |
| Lean Pool | — | — | 9/10<br>90.0% [59.6%, 98.2%] | 8/10<br>80.0% [49.0%, 94.3%] | — |
| OpenAI Math | 16/22<br>72.7% [51.8%, 86.8%] | 56/70<br>80.0% [69.2%, 87.7%] | 27/40<br>67.5% [52.0%, 79.9%] | 24/48<br>50.0% [36.4%, 63.6%] | — |

### Model comparison

Full-pass reference: **30 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 100 | 0/1 | 22/100 | 16 | 16 | 72.7% [51.8%, 86.8%] | $7.60 / $10.37 |
| Sol | 100 | 0/1 | 70/100 | 56 | 56 | 80.0% [69.2%, 87.7%] | $9.35 / $4.01 |
| Sonnet | 130 | 0/1 | 70/130 | 45 | 45 | 64.3% [52.6%, 74.5%] | $7.96 / $3.41 |
| Luna | 130 | 0/1 | 78/130 | 35 | 35 | 44.9% [34.3%, 55.9%] | $0.38 / $0.14 |
| DeepSeek | 40 | 0/1 | 0/40 | 0 | 0 | — | $0.00 / — |

#### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | 0.24 [-0.22, 0.70]; n=22 | 0.54 [0.05, 0.90]; n=22 | 0.41 [0.01, 0.73]; n=22 | — |
| Sol | 0.24 [-0.22, 0.70]; n=22 | — | 0.65 [0.37, 0.87]; n=40 | 0.37 [0.13, 0.58]; n=48 | — |
| Sonnet | 0.54 [0.05, 0.90]; n=22 | 0.65 [0.37, 0.87]; n=40 | — | 0.46 [0.28, 0.63]; n=70 | — |
| Luna | 0.41 [0.01, 0.73]; n=22 | 0.37 [0.13, 0.58]; n=48 | 0.46 [0.28, 0.63]; n=70 | — | — |
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
| OpenAI Math | 0/22<br>0.0% [0.0%, 14.9%] | 0/70<br>0.0% [0.0%, 5.2%] | 2/40<br>5.0% [1.4%, 16.5%] | 1/47<br>2.1% [0.4%, 11.1%] | — |

### Model comparison

Full-pass reference: **30 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 100 | 0/1 | 22/100 | 0 | 0 | 0.0% [0.0%, 14.9%] | $4.88 / $6.66 |
| Sol | 100 | 0/1 | 70/100 | 0 | 0 | 0.0% [0.0%, 5.2%] | $7.02 / $3.01 |
| Sonnet | 130 | 0/1 | 70/130 | 7 | 7 | 10.0% [4.9%, 19.2%] | $6.40 / $2.74 |
| Luna | 130 | 0/1 | 77/130 | 3 | 3 | 3.9% [1.3%, 10.8%] | $0.35 / $0.14 |
| DeepSeek | 40 | 0/1 | 0/40 | 0 | 0 | — | $0.00 / — |

#### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | —; n=22 | —; n=22 | —; n=22 | — |
| Sol | —; n=22 | — | —; n=40 | —; n=47 | — |
| Sonnet | —; n=22 | —; n=40 | — | -0.07 [—]; n=70 | — |
| Luna | —; n=22 | —; n=47 | -0.07 [—]; n=70 | — | — |
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
| OpenAI Math | 13/22<br>59.1% [38.7%, 76.7%] | 22/70<br>31.4% [21.8%, 43.0%] | 23/40<br>57.5% [42.2%, 71.5%] | 13/47<br>27.7% [16.9%, 41.8%] | — |

### Model comparison

Full-pass reference: **30 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 100 | 0/1 | 22/100 | 13 | 13 | 59.1% [38.7%, 76.7%] | $6.52 / $8.90 |
| Sol | 100 | 0/1 | 70/100 | 22 | 22 | 31.4% [21.8%, 43.0%] | $7.10 / $3.04 |
| Sonnet | 130 | 0/1 | 70/130 | 36 | 36 | 51.4% [40.0%, 62.8%] | $6.10 / $2.61 |
| Luna | 130 | 0/1 | 77/130 | 24 | 24 | 31.2% [21.9%, 42.2%] | $0.36 / $0.14 |
| DeepSeek | 40 | 0/1 | 0/40 | 0 | 0 | — | $0.00 / — |

#### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | 0.57 [0.32, 0.83]; n=22 | 0.73 [0.41, 1.00]; n=22 | 0.37 [-0.02, 0.69]; n=22 | — |
| Sol | 0.57 [0.32, 0.83]; n=22 | — | 0.56 [0.32, 0.77]; n=40 | 0.49 [0.20, 0.76]; n=47 | — |
| Sonnet | 0.73 [0.41, 1.00]; n=22 | 0.56 [0.32, 0.77]; n=40 | — | 0.28 [0.07, 0.50]; n=70 | — |
| Luna | 0.37 [-0.02, 0.69]; n=22 | 0.49 [0.20, 0.76]; n=47 | 0.28 [0.07, 0.50]; n=70 | — | — |
| DeepSeek | — | — | — | — | — |

Coverage annotations: Opus: 0 partial, 3 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 4 not applicable; Luna: 0 partial, 0 not applicable; DeepSeek: 0 partial, 0 not applicable.

## repeated-proof-machinery

[Library breakdowns](runs/file-quality-pilot-2026-10-21/reports/repeated-proof-machinery-comparison.md)

### Library comparison

| Library | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Mathlib | — | — | 2/10<br>20.0% [5.7%, 51.0%] | 2/10<br>20.0% [5.7%, 51.0%] | — |
| Tau Ceti | — | — | 2/10<br>20.0% [5.7%, 51.0%] | 0/10<br>0.0% [0.0%, 27.8%] | — |
| Lean Pool | — | — | 6/10<br>60.0% [31.3%, 83.2%] | 3/10<br>30.0% [10.8%, 60.3%] | — |
| OpenAI Math | 9/22<br>40.9% [23.3%, 61.3%] | 12/69<br>17.4% [10.2%, 28.0%] | 14/40<br>35.0% [22.1%, 50.5%] | 12/47<br>25.5% [15.3%, 39.5%] | — |

### Model comparison

Full-pass reference: **30 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 100 | 0/1 | 22/100 | 9 | 9 | 40.9% [23.3%, 61.3%] | $5.56 / $7.59 |
| Sol | 100 | 0/1 | 69/100 | 12 | 12 | 17.4% [10.2%, 28.0%] | $5.50 / $2.39 |
| Sonnet | 130 | 0/1 | 70/130 | 24 | 24 | 34.3% [24.2%, 46.0%] | $5.22 / $2.24 |
| Luna | 130 | 0/1 | 77/130 | 17 | 17 | 22.1% [14.3%, 32.5%] | $0.28 / $0.11 |
| DeepSeek | 40 | 0/1 | 0/40 | 0 | 0 | — | $0.00 / — |

#### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | 0.43 [-0.01, 0.79]; n=22 | 0.62 [0.25, 0.91]; n=22 | 0.57 [0.29, 0.82]; n=22 | — |
| Sol | 0.43 [-0.01, 0.79]; n=22 | — | 0.42 [0.10, 0.70]; n=40 | 0.48 [0.15, 0.76]; n=47 | — |
| Sonnet | 0.62 [0.25, 0.91]; n=22 | 0.42 [0.10, 0.70]; n=40 | — | 0.50 [0.28, 0.70]; n=70 | — |
| Luna | 0.57 [0.29, 0.82]; n=22 | 0.48 [0.15, 0.76]; n=47 | 0.50 [0.28, 0.70]; n=70 | — | — |
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
| OpenAI Math | 18/22<br>81.8% [61.5%, 92.7%] | 55/68<br>80.9% [70.0%, 88.5%] | 31/40<br>77.5% [62.5%, 87.7%] | 9/47<br>19.1% [10.4%, 32.5%] | — |

### Model comparison

Full-pass reference: **30 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 100 | 0/1 | 22/100 | 18 | 18 | 81.8% [61.5%, 92.7%] | $7.53 / $10.27 |
| Sol | 100 | 0/1 | 68/100 | 55 | 55 | 80.9% [70.0%, 88.5%] | $8.70 / $3.84 |
| Sonnet | 130 | 0/1 | 70/130 | 55 | 55 | 78.6% [67.6%, 86.6%] | $9.36 / $4.01 |
| Luna | 130 | 0/1 | 77/130 | 20 | 20 | 26.0% [17.5%, 36.7%] | $0.31 / $0.12 |
| DeepSeek | 40 | 0/1 | 0/40 | 0 | 0 | — | $0.00 / — |

#### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | 0.44 [-0.10, 0.79]; n=22 | 0.59 [-0.05, 1.00]; n=22 | 0.26 [0.10, 0.43]; n=22 | — |
| Sol | 0.44 [-0.10, 0.79]; n=22 | — | 0.52 [0.17, 0.81]; n=40 | -0.11 [-0.42, 0.19]; n=47 | — |
| Sonnet | 0.59 [-0.05, 1.00]; n=22 | 0.52 [0.17, 0.81]; n=40 | — | 0.23 [0.04, 0.36]; n=70 | — |
| Luna | 0.26 [0.10, 0.43]; n=22 | -0.11 [-0.42, 0.19]; n=47 | 0.23 [0.04, 0.36]; n=70 | — | — |
| DeepSeek | — | — | — | — | — |

Coverage annotations: Opus: 0 partial, 1 not applicable; Sol: 0 partial, 1 not applicable; Sonnet: 0 partial, 1 not applicable; Luna: 0 partial, 1 not applicable; DeepSeek: 0 partial, 0 not applicable.
