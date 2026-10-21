# Audit results

Generated 2026-10-21T05:54:53+00:00 · [Methods and notation](AUDIT_METHODS.md) · [Cost summary](runs/main/api-equivalent-costs.md).

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
| OpenAI Math | 0/1<br>0.0% [0.0%, 79.3%] | 0/1<br>0.0% [0.0%, 79.3%] | 0/2<br>0.0% [0.0%, 65.8%] | 0/2<br>0.0% [0.0%, 65.8%] |

### File audits: library comparison

Contributing audits: [concept-reinvention](#concept-reinvention), [statement-generality](#statement-generality), [vacuity-and-misstatement](#vacuity-and-misstatement), [simp-interface](#simp-interface), [repeated-proof-machinery](#repeated-proof-machinery), [readable-proof-simplification](#readable-proof-simplification).

| Library | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Mathlib | — | — | 10/10<br>100.0% [72.2%, 100.0%] | 8/10<br>80.0% [49.0%, 94.3%] |
| Tau Ceti | — | — | 9/10<br>90.0% [59.6%, 98.2%] | 4/10<br>40.0% [16.8%, 68.7%] |
| Lean Pool | — | — | 9/10<br>90.0% [59.6%, 98.2%] | 8/10<br>80.0% [49.0%, 94.3%] |
| OpenAI Math | — | — | 2/2<br>100.0% [34.2%, 100.0%] | 1/1<br>100.0% [20.7%, 100.0%] |

### Model comparison

| Model | Audits with results | Theorems selected | Files selected | Audit passes done/planned | Theorems flagged / reviewed | Files flagged / reviewed | Judgments done/planned | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| Opus | 6/8 | 4500 | 100 | 1/9 | 277/1601 | — | 7506/8300 | $472.29 / — |
| Sol | 7/8 | 5100 | 100 | 1/9 | 601/1501 | — | 8007/8800 | $460.88 / — |
| Sonnet | 8/8 | 5100 | 130 | 1/9 | 256/1502 | 30/32 | 8197/8980 | $247.08 / $210.75 |
| Luna | 8/8 | 5100 | 130 | 1/9 | 521/1502 | 21/31 | 8193/8980 | $23.37 / $21.15 |

### Theorem union correlations

| Model | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Opus | 0.92 [0.89, 0.95]; n=1500 | 0.67 [0.64, 0.71]; n=1201 | 0.80 [0.75, 0.84]; n=1201 | 0.55 [0.50, 0.60]; n=1201 |
| Sol | 0.67 [0.64, 0.71]; n=1201 | 0.99 [0.97, 1.00]; n=1500 | 0.53 [0.49, 0.56]; n=1501 | 0.65 [0.61, 0.69]; n=1501 |
| Sonnet | 0.80 [0.75, 0.84]; n=1201 | 0.53 [0.49, 0.56]; n=1501 | 0.87 [0.83, 0.92]; n=1500 | 0.50 [0.46, 0.54]; n=1502 |
| Luna | 0.55 [0.50, 0.60]; n=1201 | 0.65 [0.61, 0.69]; n=1501 | 0.50 [0.46, 0.54]; n=1502 | 0.73 [0.66, 0.78]; n=1500 |

### File union correlations

| Model | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Opus | — | —; n=1 | —; n=1 | —; n=1 |
| Sol | —; n=1 | — | —; n=1 | —; n=1 |
| Sonnet | —; n=1 | —; n=1 | — | 0.38 [—]; n=31 |
| Luna | —; n=1 | —; n=1 | 0.38 [—]; n=31 | — |

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
| OpenAI Math | 0/1<br>0.0% [0.0%, 79.3%] | 0/1<br>0.0% [0.0%, 79.3%] | 0/3<br>0.0% [0.0%, 56.2%] | 0/2<br>0.0% [0.0%, 65.8%] |

### Model comparison

Full-pass reference: **2000 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 2100 | 1/2 | 3501/3600 | 348 | 205 | 9.9% [8.7%, 11.3%] | $254.38 / $145.32 |
| Sol | 1600 | 1/2 | 3001/3100 | 374 | 189 | 12.5% [10.9%, 14.2%] | $140.75 / $93.81 |
| Sonnet | 1600 | 1/2 | 3003/3100 | 245 | 137 | 8.1% [6.8%, 9.5%] | $105.53 / $70.28 |
| Luna | 1600 | 1/2 | 3002/3100 | 310 | 193 | 10.3% [8.9%, 12.0%] | $6.51 / $4.34 |

#### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Opus | 0.92 [0.89, 0.95]; n=1500 | 0.91 [0.87, 0.94]; n=1501 | 0.85 [0.80, 0.89]; n=1501 | 0.73 [0.67, 0.78]; n=1501 |
| Sol | 0.91 [0.87, 0.94]; n=1501 | 0.99 [0.97, 1.00]; n=1500 | 0.78 [0.73, 0.82]; n=1501 | 0.70 [0.64, 0.76]; n=1501 |
| Sonnet | 0.85 [0.80, 0.89]; n=1501 | 0.78 [0.73, 0.82]; n=1501 | 0.87 [0.82, 0.91]; n=1500 | 0.70 [0.64, 0.76]; n=1502 |
| Luna | 0.73 [0.67, 0.78]; n=1501 | 0.70 [0.64, 0.76]; n=1501 | 0.70 [0.64, 0.76]; n=1502 | 0.73 [0.67, 0.78]; n=1500 |

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
| OpenAI Math | 0/1<br>0.0% [0.0%, 79.3%] | 0/1<br>0.0% [0.0%, 79.3%] | 0/2<br>0.0% [0.0%, 65.8%] | 0/2<br>0.0% [0.0%, 65.8%] |

### Model comparison

Full-pass reference: **5000 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 4100 | 0/1 | 4001/4100 | 301 | 301 | 7.5% [6.7%, 8.4%] | $216.41 / $270.44 |
| Sol | 5100 | 0/1 | 5001/5100 | 1447 | 1447 | 28.9% [27.7%, 30.2%] | $319.57 / $319.51 |
| Sonnet | 5100 | 0/1 | 5002/5100 | 519 | 519 | 10.4% [9.6%, 11.3%] | $125.04 / $124.99 |
| Luna | 5100 | 0/1 | 5002/5100 | 1352 | 1352 | 27.0% [25.8%, 28.3%] | $16.01 / $16.00 |

#### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Opus | — | 0.57 [0.54, 0.60]; n=4001 | 0.74 [0.70, 0.78]; n=4001 | 0.54 [0.51, 0.57]; n=4001 |
| Sol | 0.57 [0.54, 0.60]; n=4001 | — | 0.48 [0.46, 0.51]; n=5001 | 0.69 [0.67, 0.71]; n=5001 |
| Sonnet | 0.74 [0.70, 0.78]; n=4001 | 0.48 [0.46, 0.51]; n=5001 | — | 0.50 [0.47, 0.53]; n=5002 |
| Luna | 0.54 [0.51, 0.57]; n=4001 | 0.69 [0.67, 0.71]; n=5001 | 0.50 [0.47, 0.53]; n=5002 | — |

## concept-reinvention

[Library breakdowns](runs/file-quality-pilot-2026-10-21/reports/concept-reinvention-comparison.md)

### Library comparison

| Library | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Mathlib | — | — | 2/10<br>20.0% [5.7%, 51.0%] | 0/10<br>0.0% [0.0%, 27.8%] |
| Tau Ceti | — | — | 0/10<br>0.0% [0.0%, 27.8%] | 0/10<br>0.0% [0.0%, 27.8%] |
| Lean Pool | — | — | 4/10<br>40.0% [16.8%, 68.7%] | 0/10<br>0.0% [0.0%, 27.8%] |
| OpenAI Math | 0/1<br>0.0% [0.0%, 79.3%] | 0/1<br>0.0% [0.0%, 79.3%] | 0/2<br>0.0% [0.0%, 65.8%] | 0/2<br>0.0% [0.0%, 65.8%] |

### Model comparison

Full-pass reference: **30 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 100 | 0/1 | 1/100 | 0 | 0 | 0.0% [0.0%, 79.3%] | $0.13 / $3.78 |
| Sol | 100 | 0/1 | 1/100 | 0 | 0 | 0.0% [0.0%, 79.3%] | $0.09 / $2.57 |
| Sonnet | 130 | 0/1 | 32/130 | 6 | 6 | 18.8% [8.9%, 35.3%] | $2.29 / $2.15 |
| Luna | 130 | 0/1 | 32/130 | 0 | 0 | 0.0% [0.0%, 10.7%] | $0.16 / $0.15 |

#### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Opus | — | —; n=1 | —; n=1 | —; n=1 |
| Sol | —; n=1 | — | —; n=1 | —; n=1 |
| Sonnet | —; n=1 | —; n=1 | — | —; n=32 |
| Luna | —; n=1 | —; n=1 | —; n=32 | — |

Coverage annotations: Opus: 0 partial, 1 not applicable; Sol: 0 partial, 1 not applicable; Sonnet: 0 partial, 6 not applicable; Luna: 0 partial, 0 not applicable.

## statement-generality

[Library breakdowns](runs/file-quality-pilot-2026-10-21/reports/statement-generality-comparison.md)

### Library comparison

| Library | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Mathlib | — | — | 6/10<br>60.0% [31.3%, 83.2%] | 2/10<br>20.0% [5.7%, 51.0%] |
| Tau Ceti | — | — | 3/10<br>30.0% [10.8%, 60.3%] | 1/10<br>10.0% [1.8%, 40.4%] |
| Lean Pool | — | — | 9/10<br>90.0% [59.6%, 98.2%] | 8/10<br>80.0% [49.0%, 94.3%] |
| OpenAI Math | 1/1<br>100.0% [20.7%, 100.0%] | 1/1<br>100.0% [20.7%, 100.0%] | 2/2<br>100.0% [34.2%, 100.0%] | 2/2<br>100.0% [34.2%, 100.0%] |

### Model comparison

Full-pass reference: **30 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 100 | 0/1 | 1/100 | 1 | 1 | 100.0% [20.7%, 100.0%] | $0.96 / $28.66 |
| Sol | 100 | 0/1 | 1/100 | 1 | 1 | 100.0% [20.7%, 100.0%] | $0.14 / $4.06 |
| Sonnet | 130 | 0/1 | 32/130 | 20 | 20 | 62.5% [45.3%, 77.1%] | $3.34 / $3.13 |
| Luna | 130 | 0/1 | 32/130 | 13 | 13 | 40.6% [25.5%, 57.7%] | $0.16 / $0.15 |

#### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Opus | — | —; n=1 | —; n=1 | —; n=1 |
| Sol | —; n=1 | — | —; n=1 | —; n=1 |
| Sonnet | —; n=1 | —; n=1 | — | 0.38 [0.09, 0.64]; n=32 |
| Luna | —; n=1 | —; n=1 | 0.38 [0.09, 0.64]; n=32 | — |

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 0 not applicable; Luna: 0 partial, 0 not applicable.

## vacuity-and-misstatement

[Library breakdowns](runs/file-quality-pilot-2026-10-21/reports/vacuity-and-misstatement-comparison.md)

### Library comparison

| Library | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Mathlib | — | — | 3/10<br>30.0% [10.8%, 60.3%] | 1/10<br>10.0% [1.8%, 40.4%] |
| Tau Ceti | — | — | 0/10<br>0.0% [0.0%, 27.8%] | 1/10<br>10.0% [1.8%, 40.4%] |
| Lean Pool | — | — | 2/10<br>20.0% [5.7%, 51.0%] | 0/10<br>0.0% [0.0%, 27.8%] |
| OpenAI Math | 0/1<br>0.0% [0.0%, 79.3%] | 0/1<br>0.0% [0.0%, 79.3%] | 0/2<br>0.0% [0.0%, 65.8%] | 0/2<br>0.0% [0.0%, 65.8%] |

### Model comparison

Full-pass reference: **30 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 100 | 0/1 | 1/100 | 0 | 0 | 0.0% [0.0%, 79.3%] | $0.20 / $6.07 |
| Sol | 100 | 0/1 | 1/100 | 0 | 0 | 0.0% [0.0%, 79.3%] | $0.14 / $4.16 |
| Sonnet | 130 | 0/1 | 32/130 | 5 | 5 | 15.6% [6.9%, 31.8%] | $2.42 / $2.27 |
| Luna | 130 | 0/1 | 32/130 | 2 | 2 | 6.2% [1.7%, 20.1%] | $0.14 / $0.13 |

#### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Opus | — | —; n=1 | —; n=1 | —; n=1 |
| Sol | —; n=1 | — | —; n=1 | —; n=1 |
| Sonnet | —; n=1 | —; n=1 | — | -0.11 [—]; n=32 |
| Luna | —; n=1 | —; n=1 | -0.11 [—]; n=32 | — |

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 0 not applicable; Luna: 0 partial, 0 not applicable.

## simp-interface

[Library breakdowns](runs/file-quality-pilot-2026-10-21/reports/simp-interface-comparison.md)

### Library comparison

| Library | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Mathlib | — | — | 4/10<br>40.0% [16.8%, 68.7%] | 4/10<br>40.0% [16.8%, 68.7%] |
| Tau Ceti | — | — | 3/10<br>30.0% [10.8%, 60.3%] | 1/10<br>10.0% [1.8%, 40.4%] |
| Lean Pool | — | — | 6/10<br>60.0% [31.3%, 83.2%] | 6/10<br>60.0% [31.3%, 83.2%] |
| OpenAI Math | 1/1<br>100.0% [20.7%, 100.0%] | 0/1<br>0.0% [0.0%, 79.3%] | 1/2<br>50.0% [9.5%, 90.5%] | 1/1<br>100.0% [20.7%, 100.0%] |

### Model comparison

Full-pass reference: **30 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 100 | 0/1 | 1/100 | 1 | 1 | 100.0% [20.7%, 100.0%] | $0.22 / $6.59 |
| Sol | 100 | 0/1 | 1/100 | 0 | 0 | 0.0% [0.0%, 79.3%] | $0.09 / $2.67 |
| Sonnet | 130 | 0/1 | 32/130 | 14 | 14 | 43.8% [28.2%, 60.7%] | $2.56 / $2.40 |
| Luna | 130 | 0/1 | 31/130 | 12 | 12 | 38.7% [23.7%, 56.2%] | $0.16 / $0.15 |

#### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Opus | — | —; n=1 | —; n=1 | —; n=1 |
| Sol | —; n=1 | — | —; n=1 | —; n=1 |
| Sonnet | —; n=1 | —; n=1 | — | 0.40 [0.09, 0.68]; n=31 |
| Luna | —; n=1 | —; n=1 | 0.40 [0.09, 0.68]; n=31 | — |

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 1 not applicable; Luna: 0 partial, 0 not applicable.

## repeated-proof-machinery

[Library breakdowns](runs/file-quality-pilot-2026-10-21/reports/repeated-proof-machinery-comparison.md)

### Library comparison

| Library | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Mathlib | — | — | 2/10<br>20.0% [5.7%, 51.0%] | 2/10<br>20.0% [5.7%, 51.0%] |
| Tau Ceti | — | — | 2/10<br>20.0% [5.7%, 51.0%] | 0/10<br>0.0% [0.0%, 27.8%] |
| Lean Pool | — | — | 6/10<br>60.0% [31.3%, 83.2%] | 3/10<br>30.0% [10.8%, 60.3%] |
| OpenAI Math | — | 0/1<br>0.0% [0.0%, 79.3%] | 0/2<br>0.0% [0.0%, 65.8%] | 1/1<br>100.0% [20.7%, 100.0%] |

### Model comparison

Full-pass reference: **30 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 100 | 0/1 | 0/100 | 0 | 0 | — | $0.00 / — |
| Sol | 100 | 0/1 | 1/100 | 0 | 0 | 0.0% [0.0%, 79.3%] | $0.10 / $3.00 |
| Sonnet | 130 | 0/1 | 32/130 | 10 | 10 | 31.2% [18.0%, 48.6%] | $2.15 / $2.01 |
| Luna | 130 | 0/1 | 31/130 | 6 | 6 | 19.4% [9.2%, 36.3%] | $0.11 / $0.11 |

#### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Opus | — | — | — | — |
| Sol | — | — | —; n=1 | —; n=1 |
| Sonnet | — | —; n=1 | — | 0.54 [0.21, 0.77]; n=31 |
| Luna | — | —; n=1 | 0.54 [0.21, 0.77]; n=31 | — |

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 1 not applicable; Luna: 0 partial, 0 not applicable.

## readable-proof-simplification

[Library breakdowns](runs/file-quality-pilot-2026-10-21/reports/readable-proof-simplification-comparison.md)

### Library comparison

| Library | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Mathlib | — | — | 7/10<br>70.0% [39.7%, 89.2%] | 2/10<br>20.0% [5.7%, 51.0%] |
| Tau Ceti | — | — | 8/10<br>80.0% [49.0%, 94.3%] | 3/10<br>30.0% [10.8%, 60.3%] |
| Lean Pool | — | — | 9/10<br>90.0% [59.6%, 98.2%] | 6/10<br>60.0% [31.3%, 83.2%] |
| OpenAI Math | — | — | 1/2<br>50.0% [9.5%, 90.5%] | 0/1<br>0.0% [0.0%, 79.3%] |

### Model comparison

Full-pass reference: **30 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 100 | 0/1 | 0/100 | 0 | 0 | — | $0.00 / — |
| Sol | 100 | 0/1 | 0/100 | 0 | 0 | — | $0.00 / — |
| Sonnet | 130 | 0/1 | 32/130 | 25 | 25 | 78.1% [61.2%, 89.0%] | $3.74 / $3.51 |
| Luna | 130 | 0/1 | 31/130 | 11 | 11 | 35.5% [21.1%, 53.1%] | $0.12 / $0.12 |

#### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna |
|---|---:|---:|---:|---:|
| Opus | — | — | — | — |
| Sol | — | — | — | — |
| Sonnet | — | — | — | 0.40 [0.24, 0.59]; n=31 |
| Luna | — | — | 0.40 [0.24, 0.59]; n=31 | — |

Coverage annotations: Opus: 0 partial, 0 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 0 not applicable; Luna: 0 partial, 0 not applicable.
