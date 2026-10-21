# Audit results

Generated 2026-10-21T05:31:38+00:00 · [Methods and notation](AUDIT_METHODS.md) · [Cost summary](runs/main/api-equivalent-costs.md).

All eight audits, comparing libraries first and models second.

## unnecessary-hypotheses

[Library breakdowns](runs/main/unnecessary-hypotheses/audit-comparison.md)

### Library comparison

| Library | Opus | Sol | Sonnet | Luna | GLM |
|---|---:|---:|---:|---:|---:|
| Mathlib | 15/400<br>3.8% [2.3%, 6.1%] | 12/300<br>4.0% [2.3%, 6.9%] | 6/300<br>2.0% [0.9%, 4.3%] | 12/300<br>4.0% [2.3%, 6.9%] | 0/2<br>0.0% [0.0%, 65.8%] |
| Tau Ceti | 23/400<br>5.8% [3.9%, 8.5%] | 19/300<br>6.3% [4.1%, 9.7%] | 12/300<br>4.0% [2.3%, 6.9%] | 19/300<br>6.3% [4.1%, 9.7%] | 1/2<br>50.0% [9.5%, 90.5%] |
| Lean Pool | 61/400<br>15.2% [12.1%, 19.1%] | 60/300<br>20.0% [15.9%, 24.9%] | 39/300<br>13.0% [9.7%, 17.3%] | 48/300<br>16.0% [12.3%, 20.6%] | 1/1<br>100.0% [20.7%, 100.0%] |
| FLT (Anthropic) | 82/400<br>20.5% [16.8%, 24.7%] | 78/300<br>26.0% [21.4%, 31.2%] | 52/300<br>17.3% [13.5%, 22.0%] | 61/300<br>20.3% [16.2%, 25.2%] | 0/1<br>0.0% [0.0%, 79.3%] |
| Formal Frontier | 17/400<br>4.2% [2.7%, 6.7%] | 18/300<br>6.0% [3.8%, 9.3%] | 12/300<br>4.0% [2.3%, 6.9%] | 15/300<br>5.0% [3.1%, 8.1%] | 0/1<br>0.0% [0.0%, 79.3%] |

### Model comparison

Full-pass reference: **2000 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 2000 | 2/2 | 3500/3500 | 348 | 205 | 9.9% [8.7%, 11.3%] | $254.27 / $145.30 |
| Sol | 1500 | 2/2 | 3000/3000 | 374 | 189 | 12.5% [10.9%, 14.2%] | $140.71 / $93.81 |
| Sonnet | 1500 | 2/2 | 3000/3000 | 245 | 137 | 8.1% [6.8%, 9.6%] | $105.40 / $70.27 |
| Luna | 1500 | 2/2 | 3000/3000 | 310 | 193 | 10.3% [8.9%, 12.0%] | $6.51 / $4.34 |
| GLM | 50 | 0/1 | 7/50 | 2 | 2 | 28.6% [8.2%, 64.1%] | $0.89 / $255.14 |

#### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | GLM |
|---|---:|---:|---:|---:|---:|
| Opus | 0.92 [0.89, 0.95]; n=1500 | 0.91 [0.87, 0.94]; n=1500 | 0.85 [0.80, 0.89]; n=1500 | 0.73 [0.67, 0.78]; n=1500 | 1.00 [—]; n=7 |
| Sol | 0.91 [0.87, 0.94]; n=1500 | 0.99 [0.97, 1.00]; n=1500 | 0.78 [0.73, 0.82]; n=1500 | 0.70 [0.64, 0.76]; n=1500 | 1.00 [—]; n=7 |
| Sonnet | 0.85 [0.80, 0.89]; n=1500 | 0.78 [0.73, 0.82]; n=1500 | 0.87 [0.82, 0.91]; n=1500 | 0.70 [0.64, 0.76]; n=1500 | 1.00 [—]; n=7 |
| Luna | 0.73 [0.67, 0.78]; n=1500 | 0.70 [0.64, 0.76]; n=1500 | 0.70 [0.64, 0.76]; n=1500 | 0.73 [0.67, 0.78]; n=1500 | 1.00 [—]; n=7 |
| GLM | 1.00 [—]; n=7 | 1.00 [—]; n=7 | 1.00 [—]; n=7 | 1.00 [—]; n=7 | — |

## duplicates-mathlib-inclusive

[Library breakdowns](runs/main/duplicates-mathlib-inclusive/audit-comparison.md)

Opus uses the earlier prompt on four libraries, without Mathlib targets.

### Library comparison

| Library | Opus | Sol | Sonnet | Luna | GLM |
|---|---:|---:|---:|---:|---:|
| Mathlib | — | 689/1000<br>68.9% [66.0%, 71.7%] | 263/1000<br>26.3% [23.7%, 29.1%] | 596/1000<br>59.6% [56.5%, 62.6%] | 2/2<br>100.0% [34.2%, 100.0%] |
| Tau Ceti | 50/1000<br>5.0% [3.8%, 6.5%] | 142/1000<br>14.2% [12.2%, 16.5%] | 35/1000<br>3.5% [2.5%, 4.8%] | 150/1000<br>15.0% [12.9%, 17.3%] | 0/1<br>0.0% [0.0%, 79.3%] |
| Lean Pool | 68/1000<br>6.8% [5.4%, 8.5%] | 149/1000<br>14.9% [12.8%, 17.2%] | 58/1000<br>5.8% [4.5%, 7.4%] | 147/1000<br>14.7% [12.6%, 17.0%] | 0/1<br>0.0% [0.0%, 79.3%] |
| FLT (Anthropic) | 137/1000<br>13.7% [11.7%, 16.0%] | 255/1000<br>25.5% [22.9%, 28.3%] | 118/1000<br>11.8% [9.9%, 13.9%] | 230/1000<br>23.0% [20.5%, 25.7%] | 1/1<br>100.0% [20.7%, 100.0%] |
| Formal Frontier | 46/1000<br>4.6% [3.5%, 6.1%] | 212/1000<br>21.2% [18.8%, 23.8%] | 45/1000<br>4.5% [3.4%, 6.0%] | 229/1000<br>22.9% [20.4%, 25.6%] | 0/1<br>0.0% [0.0%, 79.3%] |

### Model comparison

Full-pass reference: **5000 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 4000 | 1/1 | 4000/4000 | 301 | 301 | 7.5% [6.7%, 8.4%] | $216.29 / $270.36 |
| Sol | 5000 | 1/1 | 5000/5000 | 1447 | 1447 | 28.9% [27.7%, 30.2%] | $319.51 / $319.51 |
| Sonnet | 5000 | 1/1 | 5000/5000 | 519 | 519 | 10.4% [9.6%, 11.3%] | $124.97 / $124.97 |
| Luna | 5000 | 1/1 | 5000/5000 | 1352 | 1352 | 27.0% [25.8%, 28.3%] | $16.00 / $16.00 |
| GLM | 50 | 0/1 | 6/50 | 3 | 3 | 50.0% [18.8%, 81.2%] | $0.18 / $150.98 |

#### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | GLM |
|---|---:|---:|---:|---:|---:|
| Opus | — | 0.57 [0.54, 0.60]; n=4000 | 0.74 [0.70, 0.78]; n=4000 | 0.54 [0.51, 0.57]; n=4000 | —; n=4 |
| Sol | 0.57 [0.54, 0.60]; n=4000 | — | 0.48 [0.46, 0.51]; n=5000 | 0.69 [0.67, 0.71]; n=5000 | 0.71 [0.71, 0.71]; n=6 |
| Sonnet | 0.74 [0.70, 0.78]; n=4000 | 0.48 [0.46, 0.51]; n=5000 | — | 0.50 [0.47, 0.53]; n=5000 | 0.45 [—]; n=6 |
| Luna | 0.54 [0.51, 0.57]; n=4000 | 0.69 [0.67, 0.71]; n=5000 | 0.50 [0.47, 0.53]; n=5000 | — | 0.71 [0.71, 0.71]; n=6 |
| GLM | —; n=4 | 0.71 [0.71, 0.71]; n=6 | 0.45 [—]; n=6 | 0.71 [0.71, 0.71]; n=6 | — |

## concept-reinvention

[Library breakdowns](runs/file-quality-pilot-2026-10-21/reports/concept-reinvention-comparison.md)

### Library comparison

| Library | Sonnet | Luna | GLM |
|---|---:|---:|---:|
| Mathlib | 2/10<br>20.0% [5.7%, 51.0%] | 0/9<br>0.0% [0.0%, 29.9%] | — |
| Tau Ceti | 0/10<br>0.0% [0.0%, 27.8%] | 0/8<br>0.0% [0.0%, 32.4%] | — |
| Lean Pool | 4/10<br>40.0% [16.8%, 68.7%] | 0/8<br>0.0% [0.0%, 32.4%] | — |

### Model comparison

Full-pass reference: **30 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Sonnet | 30 | 1/1 | 30/30 | 6 | 6 | 20.0% [9.5%, 37.3%] | $2.19 / $2.19 |
| Luna | 30 | 0/1 | 25/30 | 0 | 0 | 0.0% [0.0%, 13.3%] | $0.13 / $0.16 |
| GLM | 30 | 0/1 | 0/30 | 0 | 0 | — | $0.00 / — |

#### Correlation matrix

| Model | Sonnet | Luna | GLM |
|---|---:|---:|---:|
| Sonnet | — | —; n=25 | — |
| Luna | —; n=25 | — | — |
| GLM | — | — | — |

Coverage annotations: Sonnet: 0 partial, 5 not applicable; Luna: 0 partial, 0 not applicable; GLM: 0 partial, 0 not applicable.

## statement-generality

[Library breakdowns](runs/file-quality-pilot-2026-10-21/reports/statement-generality-comparison.md)

### Library comparison

| Library | Sonnet | Luna | GLM |
|---|---:|---:|---:|
| Mathlib | 6/10<br>60.0% [31.3%, 83.2%] | 2/9<br>22.2% [6.3%, 54.7%] | — |
| Tau Ceti | 3/10<br>30.0% [10.8%, 60.3%] | 1/9<br>11.1% [2.0%, 43.5%] | — |
| Lean Pool | 9/10<br>90.0% [59.6%, 98.2%] | 7/9<br>77.8% [45.3%, 93.7%] | — |

### Model comparison

Full-pass reference: **30 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Sonnet | 30 | 1/1 | 30/30 | 18 | 18 | 60.0% [42.3%, 75.4%] | $3.07 / $3.07 |
| Luna | 30 | 0/1 | 27/30 | 10 | 10 | 37.0% [21.5%, 55.8%] | $0.13 / $0.15 |
| GLM | 30 | 0/1 | 0/30 | 0 | 0 | — | $0.00 / — |

#### Correlation matrix

| Model | Sonnet | Luna | GLM |
|---|---:|---:|---:|
| Sonnet | — | 0.32 [0.02, 0.59]; n=27 | — |
| Luna | 0.32 [0.02, 0.59]; n=27 | — | — |
| GLM | — | — | — |

Coverage annotations: Sonnet: 0 partial, 0 not applicable; Luna: 0 partial, 0 not applicable; GLM: 0 partial, 0 not applicable.

## vacuity-and-misstatement

[Library breakdowns](runs/file-quality-pilot-2026-10-21/reports/vacuity-and-misstatement-comparison.md)

### Library comparison

| Library | Sonnet | Luna | GLM |
|---|---:|---:|---:|
| Mathlib | 3/10<br>30.0% [10.8%, 60.3%] | 1/9<br>11.1% [2.0%, 43.5%] | — |
| Tau Ceti | 0/10<br>0.0% [0.0%, 27.8%] | 1/9<br>11.1% [2.0%, 43.5%] | — |
| Lean Pool | 2/10<br>20.0% [5.7%, 51.0%] | 0/9<br>0.0% [0.0%, 29.9%] | — |

### Model comparison

Full-pass reference: **30 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Sonnet | 30 | 1/1 | 30/30 | 5 | 5 | 16.7% [7.3%, 33.6%] | $2.24 / $2.24 |
| Luna | 30 | 0/1 | 27/30 | 2 | 2 | 7.4% [2.1%, 23.4%] | $0.12 / $0.14 |
| GLM | 30 | 0/1 | 0/30 | 0 | 0 | — | $0.00 / — |

#### Correlation matrix

| Model | Sonnet | Luna | GLM |
|---|---:|---:|---:|
| Sonnet | — | -0.13 [—]; n=27 | — |
| Luna | -0.13 [—]; n=27 | — | — |
| GLM | — | — | — |

Coverage annotations: Sonnet: 0 partial, 0 not applicable; Luna: 0 partial, 0 not applicable; GLM: 0 partial, 0 not applicable.

## simp-interface

[Library breakdowns](runs/file-quality-pilot-2026-10-21/reports/simp-interface-comparison.md)

### Library comparison

| Library | Sonnet | Luna | GLM |
|---|---:|---:|---:|
| Mathlib | 4/10<br>40.0% [16.8%, 68.7%] | 3/9<br>33.3% [12.1%, 64.6%] | — |
| Tau Ceti | 3/10<br>30.0% [10.8%, 60.3%] | 1/9<br>11.1% [2.0%, 43.5%] | — |
| Lean Pool | 6/10<br>60.0% [31.3%, 83.2%] | 5/9<br>55.6% [26.7%, 81.1%] | — |

### Model comparison

Full-pass reference: **30 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Sonnet | 30 | 1/1 | 30/30 | 13 | 13 | 43.3% [27.4%, 60.8%] | $2.39 / $2.39 |
| Luna | 30 | 0/1 | 27/30 | 9 | 9 | 33.3% [18.6%, 52.2%] | $0.14 / $0.15 |
| GLM | 30 | 0/1 | 0/30 | 0 | 0 | — | $0.00 / — |

#### Correlation matrix

| Model | Sonnet | Luna | GLM |
|---|---:|---:|---:|
| Sonnet | — | 0.47 [0.16, 0.77]; n=27 | — |
| Luna | 0.47 [0.16, 0.77]; n=27 | — | — |
| GLM | — | — | — |

Coverage annotations: Sonnet: 0 partial, 1 not applicable; Luna: 0 partial, 0 not applicable; GLM: 0 partial, 0 not applicable.

## repeated-proof-machinery

[Library breakdowns](runs/file-quality-pilot-2026-10-21/reports/repeated-proof-machinery-comparison.md)

### Library comparison

| Library | Sonnet | Luna | GLM |
|---|---:|---:|---:|
| Mathlib | 2/10<br>20.0% [5.7%, 51.0%] | 2/8<br>25.0% [7.1%, 59.1%] | — |
| Tau Ceti | 2/10<br>20.0% [5.7%, 51.0%] | 0/8<br>0.0% [0.0%, 32.4%] | — |
| Lean Pool | 6/10<br>60.0% [31.3%, 83.2%] | 3/8<br>37.5% [13.7%, 69.4%] | — |

### Model comparison

Full-pass reference: **30 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Sonnet | 30 | 1/1 | 30/30 | 10 | 10 | 33.3% [19.2%, 51.2%] | $2.06 / $2.06 |
| Luna | 30 | 0/1 | 24/30 | 5 | 5 | 20.8% [9.2%, 40.5%] | $0.09 / $0.11 |
| GLM | 30 | 0/1 | 0/30 | 0 | 0 | — | $0.00 / — |

#### Correlation matrix

| Model | Sonnet | Luna | GLM |
|---|---:|---:|---:|
| Sonnet | — | 0.61 [0.36, 0.84]; n=24 | — |
| Luna | 0.61 [0.36, 0.84]; n=24 | — | — |
| GLM | — | — | — |

Coverage annotations: Sonnet: 0 partial, 1 not applicable; Luna: 0 partial, 0 not applicable; GLM: 0 partial, 0 not applicable.

## readable-proof-simplification

[Library breakdowns](runs/file-quality-pilot-2026-10-21/reports/readable-proof-simplification-comparison.md)

### Library comparison

| Library | Sonnet | Luna | GLM |
|---|---:|---:|---:|
| Mathlib | 7/10<br>70.0% [39.7%, 89.2%] | 2/9<br>22.2% [6.3%, 54.7%] | — |
| Tau Ceti | 8/10<br>80.0% [49.0%, 94.3%] | 3/9<br>33.3% [12.1%, 64.6%] | — |
| Lean Pool | 9/10<br>90.0% [59.6%, 98.2%] | 6/9<br>66.7% [35.4%, 87.9%] | — |

### Model comparison

Full-pass reference: **30 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Sonnet | 30 | 1/1 | 30/30 | 24 | 24 | 80.0% [62.7%, 90.5%] | $3.52 / $3.52 |
| Luna | 30 | 0/1 | 27/30 | 11 | 11 | 40.7% [24.5%, 59.3%] | $0.11 / $0.12 |
| GLM | 30 | 0/1 | 0/30 | 0 | 0 | — | $0.00 / — |

#### Correlation matrix

| Model | Sonnet | Luna | GLM |
|---|---:|---:|---:|
| Sonnet | — | 0.40 [0.21, 0.59]; n=27 | — |
| Luna | 0.40 [0.21, 0.59]; n=27 | — | — |
| GLM | — | — | — |

Coverage annotations: Sonnet: 0 partial, 0 not applicable; Luna: 0 partial, 0 not applicable; GLM: 0 partial, 0 not applicable.
