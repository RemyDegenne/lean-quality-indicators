# Audit results

Generated 2026-10-21T05:47:31+00:00 · [Methods and notation](AUDIT_METHODS.md) · [Cost summary](runs/main/api-equivalent-costs.md).

## Combined summary

Union across **8 audits**: a target counts once per model if any audit flags it. First passes only; theorem and file samples are counted separately. Each rate uses only targets reviewed on **every contributing audit**; a dash means no such targets. [Aggregation details](AUDIT_METHODS.md#combined-summary).

### Theorem audits: library comparison

Contributing audits: [unnecessary-hypotheses](#unnecessary-hypotheses), [duplicates-mathlib-inclusive](#duplicates-mathlib-inclusive).

| Library | Opus | Sol | Sonnet | Luna | GLM |
|---|---:|---:|---:|---:|---:|
| Mathlib | — | 215/300<br>71.7% [66.3%, 76.5%] | 85/300<br>28.3% [23.5%, 33.7%] | 176/300<br>58.7% [53.0%, 64.1%] | 2/2<br>100.0% [34.2%, 100.0%] |
| Tau Ceti | 39/400<br>9.8% [7.2%, 13.1%] | 65/300<br>21.7% [17.4%, 26.7%] | 22/300<br>7.3% [4.9%, 10.9%] | 62/300<br>20.7% [16.5%, 25.6%] | 1/2<br>50.0% [9.5%, 90.5%] |
| Formal Frontier | 32/400<br>8.0% [5.7%, 11.1%] | 78/300<br>26.0% [21.4%, 31.2%] | 19/300<br>6.3% [4.1%, 9.7%] | 78/300<br>26.0% [21.4%, 31.2%] | 0/1<br>0.0% [0.0%, 79.3%] |
| Lean Pool | 83/400<br>20.8% [17.1%, 25.0%] | 95/300<br>31.7% [26.7%, 37.1%] | 55/300<br>18.3% [14.4%, 23.1%] | 87/300<br>29.0% [24.2%, 34.4%] | 2/2<br>100.0% [34.2%, 100.0%] |
| FLT (Anthropic) | 123/400<br>30.8% [26.4%, 35.4%] | 148/300<br>49.3% [43.7%, 55.0%] | 75/300<br>25.0% [20.4%, 30.2%] | 118/300<br>39.3% [34.0%, 45.0%] | 1/2<br>50.0% [9.5%, 90.5%] |

### File audits: library comparison

Contributing audits: [concept-reinvention](#concept-reinvention), [statement-generality](#statement-generality), [vacuity-and-misstatement](#vacuity-and-misstatement), [simp-interface](#simp-interface), [repeated-proof-machinery](#repeated-proof-machinery), [readable-proof-simplification](#readable-proof-simplification).

| Library | Opus | Sol | Sonnet | Luna | GLM |
|---|---:|---:|---:|---:|---:|
| Mathlib | — | — | 10/10<br>100.0% [72.2%, 100.0%] | 8/10<br>80.0% [49.0%, 94.3%] | — |
| Tau Ceti | — | — | 9/10<br>90.0% [59.6%, 98.2%] | 4/10<br>40.0% [16.8%, 68.7%] | — |
| Lean Pool | — | — | 9/10<br>90.0% [59.6%, 98.2%] | 8/10<br>80.0% [49.0%, 94.3%] | — |

### Model comparison

| Model | Audits with results | Theorems selected | Files selected | Audit passes done/planned | Theorems flagged / reviewed | Files flagged / reviewed | Judgments done/planned | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| Opus | 2/8 | 4400 | 0 | 3/3 | 277/1600 | — | 7500/7500 | $470.56 / $415.66 |
| Sol | 2/8 | 5000 | 0 | 3/3 | 601/1500 | — | 8000/8000 | $460.22 / $413.31 |
| Sonnet | 8/8 | 5000 | 30 | 9/9 | 256/1500 | 28/30 | 8180/8180 | $245.84 / $210.70 |
| Luna | 8/8 | 5000 | 30 | 9/9 | 521/1500 | 20/30 | 8180/8180 | $23.32 / $21.15 |
| GLM | 2/8 | 50 | 30 | 0/8 | 6/9 | — | 19/280 | $1.55 / — |

### Theorem union correlations

| Model | Opus | Sol | Sonnet | Luna | GLM |
|---|---:|---:|---:|---:|---:|
| Opus | 0.92 [0.89, 0.95]; n=1500 | 0.67 [0.64, 0.71]; n=1200 | 0.80 [0.75, 0.84]; n=1200 | 0.55 [0.50, 0.60]; n=1200 | 0.42 [0.30, 0.55]; n=7 |
| Sol | 0.67 [0.64, 0.71]; n=1200 | 0.99 [0.97, 1.00]; n=1500 | 0.53 [0.49, 0.56]; n=1500 | 0.65 [0.61, 0.69]; n=1500 | 0.50 [0.36, 0.63]; n=9 |
| Sonnet | 0.80 [0.75, 0.84]; n=1200 | 0.53 [0.49, 0.56]; n=1500 | 0.87 [0.83, 0.92]; n=1500 | 0.50 [0.46, 0.54]; n=1500 | 0.16 [-0.32, 0.55]; n=9 |
| Luna | 0.55 [0.50, 0.60]; n=1200 | 0.65 [0.61, 0.69]; n=1500 | 0.50 [0.46, 0.54]; n=1500 | 0.73 [0.66, 0.78]; n=1500 | 0.79 [0.50, 1.00]; n=9 |
| GLM | 0.42 [0.30, 0.55]; n=7 | 0.50 [0.36, 0.63]; n=9 | 0.16 [-0.32, 0.55]; n=9 | 0.79 [0.50, 1.00]; n=9 | — |

### File union correlations

| Model | Opus | Sol | Sonnet | Luna | GLM |
|---|---:|---:|---:|---:|---:|
| Opus | — | — | — | — | — |
| Sol | — | — | — | — | — |
| Sonnet | — | — | — | 0.38 [—]; n=30 | — |
| Luna | — | — | 0.38 [—]; n=30 | — | — |
| GLM | — | — | — | — | — |

## unnecessary-hypotheses

[Library breakdowns](runs/main/unnecessary-hypotheses/audit-comparison.md)

### Library comparison

| Library | Opus | Sol | Sonnet | Luna | GLM |
|---|---:|---:|---:|---:|---:|
| Mathlib | 15/400<br>3.8% [2.3%, 6.1%] | 12/300<br>4.0% [2.3%, 6.9%] | 6/300<br>2.0% [0.9%, 4.3%] | 12/300<br>4.0% [2.3%, 6.9%] | 0/2<br>0.0% [0.0%, 65.8%] |
| Tau Ceti | 23/400<br>5.8% [3.9%, 8.5%] | 19/300<br>6.3% [4.1%, 9.7%] | 12/300<br>4.0% [2.3%, 6.9%] | 19/300<br>6.3% [4.1%, 9.7%] | 1/2<br>50.0% [9.5%, 90.5%] |
| Formal Frontier | 17/400<br>4.2% [2.7%, 6.7%] | 18/300<br>6.0% [3.8%, 9.3%] | 12/300<br>4.0% [2.3%, 6.9%] | 15/300<br>5.0% [3.1%, 8.1%] | 0/2<br>0.0% [0.0%, 65.8%] |
| Lean Pool | 61/400<br>15.2% [12.1%, 19.1%] | 60/300<br>20.0% [15.9%, 24.9%] | 39/300<br>13.0% [9.7%, 17.3%] | 48/300<br>16.0% [12.3%, 20.6%] | 1/2<br>50.0% [9.5%, 90.5%] |
| FLT (Anthropic) | 82/400<br>20.5% [16.8%, 24.7%] | 78/300<br>26.0% [21.4%, 31.2%] | 52/300<br>17.3% [13.5%, 22.0%] | 61/300<br>20.3% [16.2%, 25.2%] | 0/2<br>0.0% [0.0%, 65.8%] |

### Model comparison

Full-pass reference: **2000 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 2000 | 2/2 | 3500/3500 | 348 | 205 | 9.9% [8.7%, 11.3%] | $254.27 / $145.30 |
| Sol | 1500 | 2/2 | 3000/3000 | 374 | 189 | 12.5% [10.9%, 14.2%] | $140.71 / $93.81 |
| Sonnet | 1500 | 2/2 | 3000/3000 | 245 | 137 | 8.1% [6.8%, 9.6%] | $105.40 / $70.27 |
| Luna | 1500 | 2/2 | 3000/3000 | 310 | 193 | 10.3% [8.9%, 12.0%] | $6.51 / $4.34 |
| GLM | 50 | 0/1 | 10/50 | 2 | 2 | 20.0% [5.7%, 51.0%] | $1.32 / $263.55 |

#### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | GLM |
|---|---:|---:|---:|---:|---:|
| Opus | 0.92 [0.89, 0.95]; n=1500 | 0.91 [0.87, 0.94]; n=1500 | 0.85 [0.80, 0.89]; n=1500 | 0.73 [0.67, 0.78]; n=1500 | 0.76 [—]; n=10 |
| Sol | 0.91 [0.87, 0.94]; n=1500 | 0.99 [0.97, 1.00]; n=1500 | 0.78 [0.73, 0.82]; n=1500 | 0.70 [0.64, 0.76]; n=1500 | 0.76 [—]; n=10 |
| Sonnet | 0.85 [0.80, 0.89]; n=1500 | 0.78 [0.73, 0.82]; n=1500 | 0.87 [0.82, 0.91]; n=1500 | 0.70 [0.64, 0.76]; n=1500 | 0.76 [—]; n=10 |
| Luna | 0.73 [0.67, 0.78]; n=1500 | 0.70 [0.64, 0.76]; n=1500 | 0.70 [0.64, 0.76]; n=1500 | 0.73 [0.67, 0.78]; n=1500 | 1.00 [—]; n=10 |
| GLM | 0.76 [—]; n=10 | 0.76 [—]; n=10 | 0.76 [—]; n=10 | 1.00 [—]; n=10 | — |

## duplicates-mathlib-inclusive

[Library breakdowns](runs/main/duplicates-mathlib-inclusive/audit-comparison.md)

Opus uses the earlier prompt on four libraries, without Mathlib targets.

### Library comparison

| Library | Opus | Sol | Sonnet | Luna | GLM |
|---|---:|---:|---:|---:|---:|
| Mathlib | — | 689/1000<br>68.9% [66.0%, 71.7%] | 263/1000<br>26.3% [23.7%, 29.1%] | 596/1000<br>59.6% [56.5%, 62.6%] | 2/2<br>100.0% [34.2%, 100.0%] |
| Tau Ceti | 50/1000<br>5.0% [3.8%, 6.5%] | 142/1000<br>14.2% [12.2%, 16.5%] | 35/1000<br>3.5% [2.5%, 4.8%] | 150/1000<br>15.0% [12.9%, 17.3%] | 0/2<br>0.0% [0.0%, 65.8%] |
| Formal Frontier | 46/1000<br>4.6% [3.5%, 6.1%] | 212/1000<br>21.2% [18.8%, 23.8%] | 45/1000<br>4.5% [3.4%, 6.0%] | 229/1000<br>22.9% [20.4%, 25.6%] | 0/1<br>0.0% [0.0%, 79.3%] |
| Lean Pool | 68/1000<br>6.8% [5.4%, 8.5%] | 149/1000<br>14.9% [12.8%, 17.2%] | 58/1000<br>5.8% [4.5%, 7.4%] | 147/1000<br>14.7% [12.6%, 17.0%] | 1/2<br>50.0% [9.5%, 90.5%] |
| FLT (Anthropic) | 137/1000<br>13.7% [11.7%, 16.0%] | 255/1000<br>25.5% [22.9%, 28.3%] | 118/1000<br>11.8% [9.9%, 13.9%] | 230/1000<br>23.0% [20.5%, 25.7%] | 1/2<br>50.0% [9.5%, 90.5%] |

### Model comparison

Full-pass reference: **5000 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 4000 | 1/1 | 4000/4000 | 301 | 301 | 7.5% [6.7%, 8.4%] | $216.29 / $270.36 |
| Sol | 5000 | 1/1 | 5000/5000 | 1447 | 1447 | 28.9% [27.7%, 30.2%] | $319.51 / $319.51 |
| Sonnet | 5000 | 1/1 | 5000/5000 | 519 | 519 | 10.4% [9.6%, 11.3%] | $124.97 / $124.97 |
| Luna | 5000 | 1/1 | 5000/5000 | 1352 | 1352 | 27.0% [25.8%, 28.3%] | $16.00 / $16.00 |
| GLM | 50 | 0/1 | 9/50 | 4 | 4 | 44.4% [18.9%, 73.3%] | $0.24 / $131.16 |

#### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | GLM |
|---|---:|---:|---:|---:|---:|
| Opus | — | 0.57 [0.54, 0.60]; n=4000 | 0.74 [0.70, 0.78]; n=4000 | 0.54 [0.51, 0.57]; n=4000 | 0.65 [—]; n=7 |
| Sol | 0.57 [0.54, 0.60]; n=4000 | — | 0.48 [0.46, 0.51]; n=5000 | 0.69 [0.67, 0.71]; n=5000 | 0.79 [0.60, 1.00]; n=9 |
| Sonnet | 0.74 [0.70, 0.78]; n=4000 | 0.48 [0.46, 0.51]; n=5000 | — | 0.50 [0.47, 0.53]; n=5000 | 0.40 [—]; n=9 |
| Luna | 0.54 [0.51, 0.57]; n=4000 | 0.69 [0.67, 0.71]; n=5000 | 0.50 [0.47, 0.53]; n=5000 | — | 0.79 [0.60, 1.00]; n=9 |
| GLM | 0.65 [—]; n=7 | 0.79 [0.60, 1.00]; n=9 | 0.40 [—]; n=9 | 0.79 [0.60, 1.00]; n=9 | — |

## concept-reinvention

[Library breakdowns](runs/file-quality-pilot-2026-10-21/reports/concept-reinvention-comparison.md)

### Library comparison

| Library | Sonnet | Luna | GLM |
|---|---:|---:|---:|
| Mathlib | 2/10<br>20.0% [5.7%, 51.0%] | 0/10<br>0.0% [0.0%, 27.8%] | — |
| Tau Ceti | 0/10<br>0.0% [0.0%, 27.8%] | 0/10<br>0.0% [0.0%, 27.8%] | — |
| Lean Pool | 4/10<br>40.0% [16.8%, 68.7%] | 0/10<br>0.0% [0.0%, 27.8%] | — |

### Model comparison

Full-pass reference: **30 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Sonnet | 30 | 1/1 | 30/30 | 6 | 6 | 20.0% [9.5%, 37.3%] | $2.19 / $2.19 |
| Luna | 30 | 1/1 | 30/30 | 0 | 0 | 0.0% [0.0%, 11.4%] | $0.15 / $0.15 |
| GLM | 30 | 0/1 | 0/30 | 0 | 0 | — | $0.00 / — |

#### Correlation matrix

| Model | Sonnet | Luna | GLM |
|---|---:|---:|---:|
| Sonnet | — | —; n=30 | — |
| Luna | —; n=30 | — | — |
| GLM | — | — | — |

Coverage annotations: Sonnet: 0 partial, 5 not applicable; Luna: 0 partial, 0 not applicable; GLM: 0 partial, 0 not applicable.

## statement-generality

[Library breakdowns](runs/file-quality-pilot-2026-10-21/reports/statement-generality-comparison.md)

### Library comparison

| Library | Sonnet | Luna | GLM |
|---|---:|---:|---:|
| Mathlib | 6/10<br>60.0% [31.3%, 83.2%] | 2/10<br>20.0% [5.7%, 51.0%] | — |
| Tau Ceti | 3/10<br>30.0% [10.8%, 60.3%] | 1/10<br>10.0% [1.8%, 40.4%] | — |
| Lean Pool | 9/10<br>90.0% [59.6%, 98.2%] | 8/10<br>80.0% [49.0%, 94.3%] | — |

### Model comparison

Full-pass reference: **30 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Sonnet | 30 | 1/1 | 30/30 | 18 | 18 | 60.0% [42.3%, 75.4%] | $3.07 / $3.07 |
| Luna | 30 | 1/1 | 30/30 | 11 | 11 | 36.7% [21.9%, 54.5%] | $0.15 / $0.15 |
| GLM | 30 | 0/1 | 0/30 | 0 | 0 | — | $0.00 / — |

#### Correlation matrix

| Model | Sonnet | Luna | GLM |
|---|---:|---:|---:|
| Sonnet | — | 0.34 [0.05, 0.61]; n=30 | — |
| Luna | 0.34 [0.05, 0.61]; n=30 | — | — |
| GLM | — | — | — |

Coverage annotations: Sonnet: 0 partial, 0 not applicable; Luna: 0 partial, 0 not applicable; GLM: 0 partial, 0 not applicable.

## vacuity-and-misstatement

[Library breakdowns](runs/file-quality-pilot-2026-10-21/reports/vacuity-and-misstatement-comparison.md)

### Library comparison

| Library | Sonnet | Luna | GLM |
|---|---:|---:|---:|
| Mathlib | 3/10<br>30.0% [10.8%, 60.3%] | 1/10<br>10.0% [1.8%, 40.4%] | — |
| Tau Ceti | 0/10<br>0.0% [0.0%, 27.8%] | 1/10<br>10.0% [1.8%, 40.4%] | — |
| Lean Pool | 2/10<br>20.0% [5.7%, 51.0%] | 0/10<br>0.0% [0.0%, 27.8%] | — |

### Model comparison

Full-pass reference: **30 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Sonnet | 30 | 1/1 | 30/30 | 5 | 5 | 16.7% [7.3%, 33.6%] | $2.24 / $2.24 |
| Luna | 30 | 1/1 | 30/30 | 2 | 2 | 6.7% [1.8%, 21.3%] | $0.13 / $0.13 |
| GLM | 30 | 0/1 | 0/30 | 0 | 0 | — | $0.00 / — |

#### Correlation matrix

| Model | Sonnet | Luna | GLM |
|---|---:|---:|---:|
| Sonnet | — | -0.12 [—]; n=30 | — |
| Luna | -0.12 [—]; n=30 | — | — |
| GLM | — | — | — |

Coverage annotations: Sonnet: 0 partial, 0 not applicable; Luna: 0 partial, 0 not applicable; GLM: 0 partial, 0 not applicable.

## simp-interface

[Library breakdowns](runs/file-quality-pilot-2026-10-21/reports/simp-interface-comparison.md)

### Library comparison

| Library | Sonnet | Luna | GLM |
|---|---:|---:|---:|
| Mathlib | 4/10<br>40.0% [16.8%, 68.7%] | 4/10<br>40.0% [16.8%, 68.7%] | — |
| Tau Ceti | 3/10<br>30.0% [10.8%, 60.3%] | 1/10<br>10.0% [1.8%, 40.4%] | — |
| Lean Pool | 6/10<br>60.0% [31.3%, 83.2%] | 6/10<br>60.0% [31.3%, 83.2%] | — |

### Model comparison

Full-pass reference: **30 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Sonnet | 30 | 1/1 | 30/30 | 13 | 13 | 43.3% [27.4%, 60.8%] | $2.39 / $2.39 |
| Luna | 30 | 1/1 | 30/30 | 11 | 11 | 36.7% [21.9%, 54.5%] | $0.15 / $0.15 |
| GLM | 30 | 0/1 | 0/30 | 0 | 0 | — | $0.00 / — |

#### Correlation matrix

| Model | Sonnet | Luna | GLM |
|---|---:|---:|---:|
| Sonnet | — | 0.45 [0.13, 0.74]; n=30 | — |
| Luna | 0.45 [0.13, 0.74]; n=30 | — | — |
| GLM | — | — | — |

Coverage annotations: Sonnet: 0 partial, 1 not applicable; Luna: 0 partial, 0 not applicable; GLM: 0 partial, 0 not applicable.

## repeated-proof-machinery

[Library breakdowns](runs/file-quality-pilot-2026-10-21/reports/repeated-proof-machinery-comparison.md)

### Library comparison

| Library | Sonnet | Luna | GLM |
|---|---:|---:|---:|
| Mathlib | 2/10<br>20.0% [5.7%, 51.0%] | 2/10<br>20.0% [5.7%, 51.0%] | — |
| Tau Ceti | 2/10<br>20.0% [5.7%, 51.0%] | 0/10<br>0.0% [0.0%, 27.8%] | — |
| Lean Pool | 6/10<br>60.0% [31.3%, 83.2%] | 3/10<br>30.0% [10.8%, 60.3%] | — |

### Model comparison

Full-pass reference: **30 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Sonnet | 30 | 1/1 | 30/30 | 10 | 10 | 33.3% [19.2%, 51.2%] | $2.06 / $2.06 |
| Luna | 30 | 1/1 | 30/30 | 5 | 5 | 16.7% [7.3%, 33.6%] | $0.11 / $0.11 |
| GLM | 30 | 0/1 | 0/30 | 0 | 0 | — | $0.00 / — |

#### Correlation matrix

| Model | Sonnet | Luna | GLM |
|---|---:|---:|---:|
| Sonnet | — | 0.63 [0.38, 0.86]; n=30 | — |
| Luna | 0.63 [0.38, 0.86]; n=30 | — | — |
| GLM | — | — | — |

Coverage annotations: Sonnet: 0 partial, 1 not applicable; Luna: 0 partial, 0 not applicable; GLM: 0 partial, 0 not applicable.

## readable-proof-simplification

[Library breakdowns](runs/file-quality-pilot-2026-10-21/reports/readable-proof-simplification-comparison.md)

### Library comparison

| Library | Sonnet | Luna | GLM |
|---|---:|---:|---:|
| Mathlib | 7/10<br>70.0% [39.7%, 89.2%] | 2/10<br>20.0% [5.7%, 51.0%] | — |
| Tau Ceti | 8/10<br>80.0% [49.0%, 94.3%] | 3/10<br>30.0% [10.8%, 60.3%] | — |
| Lean Pool | 9/10<br>90.0% [59.6%, 98.2%] | 6/10<br>60.0% [31.3%, 83.2%] | — |

### Model comparison

Full-pass reference: **30 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Sonnet | 30 | 1/1 | 30/30 | 24 | 24 | 80.0% [62.7%, 90.5%] | $3.52 / $3.52 |
| Luna | 30 | 1/1 | 30/30 | 11 | 11 | 36.7% [21.9%, 54.5%] | $0.12 / $0.12 |
| GLM | 30 | 0/1 | 0/30 | 0 | 0 | — | $0.00 / — |

#### Correlation matrix

| Model | Sonnet | Luna | GLM |
|---|---:|---:|---:|
| Sonnet | — | 0.38 [0.20, 0.57]; n=30 | — |
| Luna | 0.38 [0.20, 0.57]; n=30 | — | — |
| GLM | — | — | — |

Coverage annotations: Sonnet: 0 partial, 0 not applicable; Luna: 0 partial, 0 not applicable; GLM: 0 partial, 0 not applicable.
