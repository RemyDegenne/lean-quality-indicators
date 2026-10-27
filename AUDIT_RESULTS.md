# Audit results

Generated 2026-10-27T19:50:33+00:00 · [Methods and notation](AUDIT_METHODS.md) · [Cost summary](runs/main/api-equivalent-costs.md).

[Appendix: simp interface and concept reinvention — not ready for use](AUDIT_APPENDIX.md). These audits do not contribute to the summaries below.

## Combined summary

Union across **7 audits**: a target counts once per model if any audit flags it. First passes only; theorem, definition and file samples are counted separately. Each rate uses only targets reviewed on **every contributing audit**; a dash means no such targets. [Aggregation details](AUDIT_METHODS.md#combined-summary).

### Theorem audits: library comparison

Contributing audits: [unnecessary-hypotheses](#unnecessary-hypotheses), [duplicates-mathlib-inclusive](#duplicates-mathlib-inclusive).

| Library | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Mathlib | — | 215/300<br>71.7% [66.3%, 76.5%] | 85/300<br>28.3% [23.5%, 33.7%] | 176/300<br>58.7% [53.0%, 64.1%] | 49/100<br>49.0% [39.4%, 58.7%] |
| Tau Ceti | 118/1000<br>11.8% [9.9%, 13.9%] | 65/300<br>21.7% [17.4%, 26.7%] | 22/300<br>7.3% [4.9%, 10.9%] | 62/300<br>20.7% [16.5%, 25.6%] | 11/100<br>11.0% [6.3%, 18.6%] |
| Formal Frontier | 79/1000<br>7.9% [6.4%, 9.7%] | 78/300<br>26.0% [21.4%, 31.2%] | 19/300<br>6.3% [4.1%, 9.7%] | 78/300<br>26.0% [21.4%, 31.2%] | 11/100<br>11.0% [6.3%, 18.6%] |
| Lean Pool | 215/1000<br>21.5% [19.1%, 24.2%] | 95/300<br>31.7% [26.7%, 37.1%] | 55/300<br>18.3% [14.4%, 23.1%] | 87/300<br>29.0% [24.2%, 34.4%] | 22/100<br>22.0% [15.0%, 31.1%] |
| FLT (Anthropic) | 319/1000<br>31.9% [29.1%, 34.9%] | 148/300<br>49.3% [43.7%, 55.0%] | 75/300<br>25.0% [20.4%, 30.2%] | 118/300<br>39.3% [34.0%, 45.0%] | 35/100<br>35.0% [26.4%, 44.7%] |
| OpenAI Math | 18/100<br>18.0% [11.7%, 26.7%] | 23/100<br>23.0% [15.8%, 32.2%] | 51/258<br>19.8% [15.4%, 25.1%] | 24/100<br>24.0% [16.7%, 33.2%] | 18/100<br>18.0% [11.7%, 26.7%] |
| CFSG (AxiomMath) | — | — | 60/227<br>26.4% [21.1%, 32.5%] | — | — |

### Definition audits: library comparison

Contributing audits: [definition-fidelity](#definition-fidelity).

| Library | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Mathlib | 10/1000<br>1.0% [0.5%, 1.8%] | — | — | — | — |
| Tau Ceti | 11/1000<br>1.1% [0.6%, 2.0%] | — | — | — | — |
| Formal Frontier | 41/1000<br>4.1% [3.0%, 5.5%] | — | — | — | — |
| Lean Pool | 33/1000<br>3.3% [2.4%, 4.6%] | — | — | — | — |
| FLT (Anthropic) | 1000/1000<br>100.0% [99.6%, 100.0%] | — | — | — | — |

### File audits: library comparison

Contributing audits: [statement-generality](#statement-generality), [vacuity-and-misstatement](#vacuity-and-misstatement), [repeated-proof-machinery](#repeated-proof-machinery), [readable-proof-simplification](#readable-proof-simplification).

| Library | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Mathlib | — | — | 10/10<br>100.0% [72.2%, 100.0%] | 6/10<br>60.0% [31.3%, 83.2%] | 10/10<br>100.0% [72.2%, 100.0%] |
| Tau Ceti | — | — | 9/10<br>90.0% [59.6%, 98.2%] | 4/10<br>40.0% [16.8%, 68.7%] | 7/10<br>70.0% [39.7%, 89.2%] |
| Formal Frontier | — | — | — | — | — |
| Lean Pool | — | — | 9/10<br>90.0% [59.6%, 98.2%] | 8/10<br>80.0% [49.0%, 94.3%] | 10/10<br>100.0% [72.2%, 100.0%] |
| FLT (Anthropic) | — | — | — | — | — |
| OpenAI Math | 95/100<br>95.0% [88.8%, 97.8%] | 93/100<br>93.0% [86.3%, 96.6%] | 91/100<br>91.0% [83.8%, 95.2%] | 61/100<br>61.0% [51.2%, 70.0%] | 9/10<br>90.0% [59.6%, 98.2%] |
| CFSG (AxiomMath) | — | — | — | — | — |

### Model comparison

| Model | Audits with results | Theorems selected | Definitions selected | Files selected | Audit passes done/planned | Theorems flagged / reviewed | Definitions flagged / reviewed | Files flagged / reviewed | Judgments done/planned | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Opus | 7/7 | 5100 | 5000 | 100 | 8/8 | 749/4100 | 1095/5000 | 95/100 | 16100/16100 | $1165.07 / $1142.01 |
| Sol | 6/7 | 5100 | 0 | 100 | 7/7 | 624/1600 | — | 93/100 | 8600/8600 | $515.64 / $622.87 |
| Sonnet | 6/7 | 5600 | 0 | 3300 | 4/7 | 367/1985 | — | 119/130 | 11835/12890 | $531.33 / $382.16 |
| Luna | 6/7 | 5100 | 0 | 130 | 7/7 | 545/1600 | — | 79/130 | 8720/8720 | $25.31 / $29.70 |
| DeepSeek | 6/7 | 600 | 0 | 40 | 6/6 | 146/600 | — | 36/40 | 1360/1360 | $10.81 / $70.78 |

### Theorem union correlations

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | 0.92 [0.89, 0.95]; n=1500 | 0.68 [0.65, 0.72]; n=1300 | 0.81 [0.76, 0.85]; n=1300 | 0.57 [0.51, 0.61]; n=1300 | 0.74 [0.66, 0.81]; n=500 |
| Sol | 0.68 [0.65, 0.72]; n=1300 | 0.99 [0.97, 1.00]; n=1500 | 0.54 [0.51, 0.57]; n=1600 | 0.66 [0.63, 0.70]; n=1600 | 0.63 [0.57, 0.69]; n=600 |
| Sonnet | 0.81 [0.76, 0.85]; n=1300 | 0.54 [0.51, 0.57]; n=1600 | 0.87 [0.83, 0.92]; n=1500 | 0.52 [0.47, 0.56]; n=1600 | 0.65 [0.57, 0.72]; n=600 |
| Luna | 0.57 [0.51, 0.61]; n=1300 | 0.66 [0.63, 0.70]; n=1600 | 0.52 [0.47, 0.56]; n=1600 | 0.73 [0.66, 0.78]; n=1500 | 0.66 [0.60, 0.72]; n=600 |
| DeepSeek | 0.74 [0.66, 0.81]; n=500 | 0.63 [0.57, 0.69]; n=600 | 0.65 [0.57, 0.72]; n=600 | 0.66 [0.60, 0.72]; n=600 | — |

### Definition union correlations

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | — | — | — | — |
| Sol | — | — | — | — | — |
| Sonnet | — | — | — | — | — |
| Luna | — | — | — | — | — |
| DeepSeek | — | — | — | — | — |

### File union correlations

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | 0.66 [0.23, 0.92]; n=100 | 0.57 [0.20, 0.84]; n=100 | 0.19 [0.00, 0.35]; n=100 | 1.00 [—]; n=10 |
| Sol | 0.66 [0.23, 0.92]; n=100 | — | 0.46 [0.09, 0.76]; n=100 | 0.10 [-0.09, 0.30]; n=100 | 1.00 [—]; n=10 |
| Sonnet | 0.57 [0.20, 0.84]; n=100 | 0.46 [0.09, 0.76]; n=100 | — | 0.38 [0.27, 0.49]; n=130 | 0.54 [—]; n=40 |
| Luna | 0.19 [0.00, 0.35]; n=100 | 0.10 [-0.09, 0.30]; n=100 | 0.38 [0.27, 0.49]; n=130 | — | 0.43 [0.22, 0.63]; n=40 |
| DeepSeek | 1.00 [—]; n=10 | 1.00 [—]; n=10 | 0.54 [—]; n=40 | 0.43 [0.22, 0.63]; n=40 | — |

## unnecessary-hypotheses

[Library breakdowns](runs/main/unnecessary-hypotheses/audit-comparison.md)

### Library comparison

| Library | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Mathlib | 31/1000<br>3.1% [2.2%, 4.4%] | 12/300<br>4.0% [2.3%, 6.9%] | 6/300<br>2.0% [0.9%, 4.3%] | 12/300<br>4.0% [2.3%, 6.9%] | 3/100<br>3.0% [1.0%, 8.5%] |
| Tau Ceti | 68/1000<br>6.8% [5.4%, 8.5%] | 19/300<br>6.3% [4.1%, 9.7%] | 12/300<br>4.0% [2.3%, 6.9%] | 19/300<br>6.3% [4.1%, 9.7%] | 5/100<br>5.0% [2.2%, 11.2%] |
| Formal Frontier | 34/1000<br>3.4% [2.4%, 4.7%] | 18/300<br>6.0% [3.8%, 9.3%] | 12/300<br>4.0% [2.3%, 6.9%] | 15/300<br>5.0% [3.1%, 8.1%] | 1/100<br>1.0% [0.2%, 5.4%] |
| Lean Pool | 150/1000<br>15.0% [12.9%, 17.3%] | 60/300<br>20.0% [15.9%, 24.9%] | 39/300<br>13.0% [9.7%, 17.3%] | 48/300<br>16.0% [12.3%, 20.6%] | 13/100<br>13.0% [7.8%, 21.0%] |
| FLT (Anthropic) | 203/1000<br>20.3% [17.9%, 22.9%] | 78/300<br>26.0% [21.4%, 31.2%] | 52/300<br>17.3% [13.5%, 22.0%] | 61/300<br>20.3% [16.2%, 25.2%] | 21/100<br>21.0% [14.2%, 30.0%] |
| OpenAI Math | 17/100<br>17.0% [10.9%, 25.5%] | 21/100<br>21.0% [14.2%, 30.0%] | 44/258<br>17.1% [13.0%, 22.1%] | 19/100<br>19.0% [12.5%, 27.8%] | 16/100<br>16.0% [10.1%, 24.4%] |
| CFSG (AxiomMath) | — | — | 50/227<br>22.0% [17.1%, 27.9%] | — | — |

### Model comparison

Full-pass reference: **5100 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 5100 | 2/2 | 6600/6600 | 653 | 510 | 9.9% [9.1%, 10.7%] | $491.63 / $379.90 |
| Sol | 1600 | 2/2 | 3100/3100 | 395 | 210 | 13.0% [11.4%, 14.7%] | $145.80 / $239.87 |
| Sonnet | 2100 | 1/2 | 3485/3600 | 339 | 231 | 10.8% [9.5%, 12.3%] | $133.09 / $194.77 |
| Luna | 1600 | 2/2 | 3100/3100 | 329 | 212 | 10.9% [9.4%, 12.5%] | $6.81 / $11.20 |
| DeepSeek | 600 | 1/1 | 600/600 | 59 | 59 | 9.8% [7.7%, 12.5%] | $4.52 / $38.46 |

#### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | 0.92 [0.89, 0.95]; n=1500 | 0.90 [0.87, 0.93]; n=1600 | 0.86 [0.82, 0.90]; n=1600 | 0.74 [0.69, 0.79]; n=1600 | 0.87 [0.80, 0.93]; n=600 |
| Sol | 0.90 [0.87, 0.93]; n=1600 | 0.99 [0.97, 1.00]; n=1500 | 0.78 [0.74, 0.82]; n=1600 | 0.72 [0.67, 0.77]; n=1600 | 0.80 [0.72, 0.86]; n=600 |
| Sonnet | 0.86 [0.82, 0.90]; n=1600 | 0.78 [0.74, 0.82]; n=1600 | 0.87 [0.82, 0.91]; n=1500 | 0.71 [0.66, 0.77]; n=1600 | 0.79 [0.70, 0.87]; n=600 |
| Luna | 0.74 [0.69, 0.79]; n=1600 | 0.72 [0.67, 0.77]; n=1600 | 0.71 [0.66, 0.77]; n=1600 | 0.73 [0.67, 0.78]; n=1500 | 0.75 [0.66, 0.83]; n=600 |
| DeepSeek | 0.87 [0.80, 0.93]; n=600 | 0.80 [0.72, 0.86]; n=600 | 0.79 [0.70, 0.87]; n=600 | 0.75 [0.66, 0.83]; n=600 | — |

## duplicates-mathlib-inclusive

[Library breakdowns](runs/main/duplicates-mathlib-inclusive/audit-comparison.md)

Opus uses the earlier prompt on four libraries, without Mathlib targets.

### Library comparison

| Library | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Mathlib | — | 689/1000<br>68.9% [66.0%, 71.7%] | 263/1000<br>26.3% [23.7%, 29.1%] | 596/1000<br>59.6% [56.5%, 62.6%] | 47/100<br>47.0% [37.5%, 56.7%] |
| Tau Ceti | 50/1000<br>5.0% [3.8%, 6.5%] | 142/1000<br>14.2% [12.2%, 16.5%] | 35/1000<br>3.5% [2.5%, 4.8%] | 150/1000<br>15.0% [12.9%, 17.3%] | 6/100<br>6.0% [2.8%, 12.5%] |
| Formal Frontier | 46/1000<br>4.6% [3.5%, 6.1%] | 212/1000<br>21.2% [18.8%, 23.8%] | 45/1000<br>4.5% [3.4%, 6.0%] | 229/1000<br>22.9% [20.4%, 25.6%] | 10/100<br>10.0% [5.5%, 17.4%] |
| Lean Pool | 68/1000<br>6.8% [5.4%, 8.5%] | 149/1000<br>14.9% [12.8%, 17.2%] | 58/1000<br>5.8% [4.5%, 7.4%] | 147/1000<br>14.7% [12.6%, 17.0%] | 9/100<br>9.0% [4.8%, 16.2%] |
| FLT (Anthropic) | 137/1000<br>13.7% [11.7%, 16.0%] | 255/1000<br>25.5% [22.9%, 28.3%] | 118/1000<br>11.8% [9.9%, 13.9%] | 230/1000<br>23.0% [20.5%, 25.7%] | 16/100<br>16.0% [10.1%, 24.4%] |
| OpenAI Math | 1/100<br>1.0% [0.2%, 5.4%] | 2/100<br>2.0% [0.6%, 7.0%] | 7/258<br>2.7% [1.3%, 5.5%] | 5/100<br>5.0% [2.2%, 11.2%] | 2/100<br>2.0% [0.6%, 7.0%] |
| CFSG (AxiomMath) | — | — | 10/227<br>4.4% [2.4%, 7.9%] | — | — |

### Model comparison

Full-pass reference: **5100 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 4100 | 1/1 | 4100/4100 | 302 | 302 | 7.4% [6.6%, 8.2%] | $222.89 / $277.26 |
| Sol | 5100 | 1/1 | 5100/5100 | 1449 | 1449 | 28.4% [27.2%, 29.7%] | $325.96 / $325.96 |
| Sonnet | 5600 | 0/1 | 5485/5600 | 536 | 536 | 9.8% [9.0%, 10.6%] | $138.76 / $129.02 |
| Luna | 5100 | 1/1 | 5100/5100 | 1357 | 1357 | 26.6% [25.4%, 27.8%] | $16.33 / $16.33 |
| DeepSeek | 600 | 1/1 | 600/600 | 90 | 90 | 15.0% [12.4%, 18.1%] | $2.26 / $19.25 |

#### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | 0.57 [0.54, 0.60]; n=4100 | 0.74 [0.70, 0.78]; n=4100 | 0.54 [0.51, 0.57]; n=4100 | 0.63 [0.48, 0.74]; n=500 |
| Sol | 0.57 [0.54, 0.60]; n=4100 | — | 0.48 [0.46, 0.51]; n=5100 | 0.69 [0.67, 0.72]; n=5100 | 0.61 [0.54, 0.68]; n=600 |
| Sonnet | 0.74 [0.70, 0.78]; n=4100 | 0.48 [0.46, 0.51]; n=5100 | — | 0.50 [0.48, 0.53]; n=5100 | 0.61 [0.51, 0.70]; n=600 |
| Luna | 0.54 [0.51, 0.57]; n=4100 | 0.69 [0.67, 0.72]; n=5100 | 0.50 [0.48, 0.53]; n=5100 | — | 0.67 [0.60, 0.73]; n=600 |
| DeepSeek | 0.63 [0.48, 0.74]; n=500 | 0.61 [0.54, 0.68]; n=600 | 0.61 [0.51, 0.70]; n=600 | 0.67 [0.60, 0.73]; n=600 | — |

## definition-fidelity

[Library breakdowns](runs/defs1/definition-fidelity/audit-comparison.md)

Opus includes automatic missing-docstring flags. Rates use all reviewed definitions. [Assessed-only rates](runs/defs1/definition-fidelity/claude-opus-5-5-high/report.md).

### Library comparison

| Library | Opus |
|---|---:|
| Mathlib | 10/1000<br>1.0% [0.5%, 1.8%] |
| Tau Ceti | 11/1000<br>1.1% [0.6%, 2.0%] |
| Formal Frontier | 41/1000<br>4.1% [3.0%, 5.5%] |
| Lean Pool | 33/1000<br>3.3% [2.4%, 4.6%] |
| FLT (Anthropic) | 1000/1000<br>100.0% [99.6%, 100.0%] |

### Model comparison

Full-pass reference: **5000 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 5000 | 1/1 | 5000/5000 | 1095 | 1095 | 21.9% [20.8%, 23.1%] | $336.14 / $336.14 |

#### Correlation matrix

| Model | Opus |
|---|---:|
| Opus | — |

## statement-generality

[Library breakdowns](runs/file-quality-pilot-2026-10-21/reports/statement-generality-comparison.md)

### Library comparison

| Library | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Mathlib | — | — | 6/10<br>60.0% [31.3%, 83.2%] | 2/10<br>20.0% [5.7%, 51.0%] | 9/10<br>90.0% [59.6%, 98.2%] |
| Tau Ceti | — | — | 3/10<br>30.0% [10.8%, 60.3%] | 1/10<br>10.0% [1.8%, 40.4%] | 6/10<br>60.0% [31.3%, 83.2%] |
| Lean Pool | — | — | 9/10<br>90.0% [59.6%, 98.2%] | 8/10<br>80.0% [49.0%, 94.3%] | 10/10<br>100.0% [72.2%, 100.0%] |
| OpenAI Math | 67/100<br>67.0% [57.3%, 75.4%] | 79/100<br>79.0% [70.0%, 85.8%] | 60/100<br>60.0% [50.2%, 69.1%] | 47/100<br>47.0% [37.5%, 56.7%] | 9/10<br>90.0% [59.6%, 98.2%] |

### Model comparison

Full-pass reference: **130 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 100 | 1/1 | 100/100 | 67 | 67 | 67.0% [57.3%, 75.4%] | $32.26 / $41.93 |
| Sol | 100 | 1/1 | 100/100 | 79 | 79 | 79.0% [70.0%, 85.8%] | $13.16 / $17.11 |
| Sonnet | 130 | 1/1 | 130/130 | 78 | 78 | 60.0% [51.4%, 68.0%] | $16.38 / $16.38 |
| Luna | 130 | 1/1 | 130/130 | 58 | 58 | 44.6% [36.3%, 53.2%] | $0.63 / $0.63 |
| DeepSeek | 40 | 1/1 | 40/40 | 34 | 34 | 85.0% [70.9%, 92.9%] | $1.17 / $3.79 |

#### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | 0.47 [0.28, 0.66]; n=100 | 0.51 [0.33, 0.67]; n=100 | 0.36 [0.18, 0.53]; n=100 | 0.51 [—]; n=10 |
| Sol | 0.47 [0.28, 0.66]; n=100 | — | 0.48 [0.30, 0.63]; n=100 | 0.39 [0.22, 0.53]; n=100 | 1.00 [—]; n=10 |
| Sonnet | 0.51 [0.33, 0.67]; n=100 | 0.48 [0.30, 0.63]; n=100 | — | 0.48 [0.34, 0.61]; n=130 | 0.43 [0.10, 0.68]; n=40 |
| Luna | 0.36 [0.18, 0.53]; n=100 | 0.39 [0.22, 0.53]; n=100 | 0.48 [0.34, 0.61]; n=130 | — | 0.38 [0.22, 0.54]; n=40 |
| DeepSeek | 0.51 [—]; n=10 | 1.00 [—]; n=10 | 0.43 [0.10, 0.68]; n=40 | 0.38 [0.22, 0.54]; n=40 | — |

Coverage annotations: Opus: 0 partial, 1 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 1 not applicable; Luna: 0 partial, 0 not applicable; DeepSeek: 0 partial, 0 not applicable.

## vacuity-and-misstatement

[Library breakdowns](runs/file-quality-pilot-2026-10-21/reports/vacuity-and-misstatement-comparison.md)

### Library comparison

| Library | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Mathlib | — | — | 3/10<br>30.0% [10.8%, 60.3%] | 1/10<br>10.0% [1.8%, 40.4%] | 5/10<br>50.0% [23.7%, 76.3%] |
| Tau Ceti | — | — | 0/10<br>0.0% [0.0%, 27.8%] | 1/10<br>10.0% [1.8%, 40.4%] | 3/10<br>30.0% [10.8%, 60.3%] |
| Lean Pool | — | — | 2/10<br>20.0% [5.7%, 51.0%] | 0/10<br>0.0% [0.0%, 27.8%] | 5/10<br>50.0% [23.7%, 76.3%] |
| OpenAI Math | 0/100<br>0.0% [0.0%, 3.7%] | 0/100<br>0.0% [0.0%, 3.7%] | 3/100<br>3.0% [1.0%, 8.5%] | 3/100<br>3.0% [1.0%, 8.5%] | 0/10<br>0.0% [0.0%, 27.8%] |

### Model comparison

Full-pass reference: **130 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 100 | 1/1 | 100/100 | 0 | 0 | 0.0% [0.0%, 3.7%] | $21.38 / $27.79 |
| Sol | 100 | 1/1 | 100/100 | 0 | 0 | 0.0% [0.0%, 3.7%] | $9.89 / $12.85 |
| Sonnet | 130 | 1/1 | 130/130 | 8 | 8 | 6.2% [3.2%, 11.7%] | $12.33 / $12.33 |
| Luna | 130 | 1/1 | 130/130 | 5 | 5 | 3.8% [1.7%, 8.7%] | $0.58 / $0.58 |
| DeepSeek | 40 | 1/1 | 40/40 | 13 | 13 | 32.5% [20.1%, 48.0%] | $1.15 / $3.73 |

#### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | —; n=100 | —; n=100 | —; n=100 | —; n=10 |
| Sol | —; n=100 | — | —; n=100 | —; n=100 | —; n=10 |
| Sonnet | —; n=100 | —; n=100 | — | 0.12 [-0.06, 0.41]; n=130 | 0.38 [0.05, 0.65]; n=40 |
| Luna | —; n=100 | —; n=100 | 0.12 [-0.06, 0.41]; n=130 | — | 0.33 [—]; n=40 |
| DeepSeek | —; n=10 | —; n=10 | 0.38 [0.05, 0.65]; n=40 | 0.33 [—]; n=40 | — |

Coverage annotations: Opus: 0 partial, 1 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 0 partial, 0 not applicable; Luna: 0 partial, 0 not applicable; DeepSeek: 0 partial, 0 not applicable.

## repeated-proof-machinery

[Library breakdowns](runs/file-quality-pilot-2026-10-21/reports/repeated-proof-machinery-comparison.md)

[Balanced validation sample](runs/repeated-machinery-validation-2026-10-27/validation-report.md) is reported separately from the first-pass counts below.

### Library comparison

| Library | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Mathlib | — | — | 60/372<br>16.1% [12.7%, 20.2%] | 2/10<br>20.0% [5.7%, 51.0%] | 2/10<br>20.0% [5.7%, 51.0%] |
| Tau Ceti | — | — | 64/372<br>17.2% [13.7%, 21.4%] | 0/10<br>0.0% [0.0%, 27.8%] | 3/10<br>30.0% [10.8%, 60.3%] |
| Formal Frontier | — | — | 128/372<br>34.4% [29.8%, 39.4%] | — | — |
| Lean Pool | — | — | 180/372<br>48.4% [43.4%, 53.5%] | 3/10<br>30.0% [10.8%, 60.3%] | 7/10<br>70.0% [39.7%, 89.2%] |
| FLT (Anthropic) | — | — | 189/372<br>50.8% [45.7%, 55.9%] | — | — |
| OpenAI Math | 48/100<br>48.0% [38.5%, 57.7%] | 20/100<br>20.0% [13.3%, 28.9%] | 154/372<br>41.4% [36.5%, 46.5%] | 20/100<br>20.0% [13.3%, 28.9%] | 5/10<br>50.0% [23.7%, 76.3%] |
| CFSG (AxiomMath) | — | — | 126/243<br>51.9% [45.6%, 58.1%] | — | — |

### Model comparison

Full-pass reference: **130 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 100 | 1/1 | 100/100 | 48 | 48 | 48.0% [38.5%, 57.7%] | $26.18 / $34.04 |
| Sol | 100 | 1/1 | 100/100 | 20 | 20 | 20.0% [13.3%, 28.9%] | $8.15 / $10.60 |
| Sonnet | 3300 | 0/1 | 2475/3300 | 901 | 901 | 36.4% [34.5%, 38.3%] | $212.25 / $11.15 |
| Luna | 130 | 1/1 | 130/130 | 25 | 25 | 19.2% [13.4%, 26.8%] | $0.46 / $0.46 |
| DeepSeek | 40 | 1/1 | 40/40 | 17 | 17 | 42.5% [28.5%, 57.8%] | $0.55 / $1.79 |

#### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | 0.42 [0.26, 0.56]; n=100 | 0.69 [0.55, 0.82]; n=100 | 0.32 [0.15, 0.49]; n=100 | 0.60 [0.00, 1.00]; n=10 |
| Sol | 0.42 [0.26, 0.56]; n=100 | — | 0.43 [0.24, 0.59]; n=100 | 0.50 [0.27, 0.69]; n=100 | 0.33 [—]; n=10 |
| Sonnet | 0.69 [0.55, 0.82]; n=100 | 0.43 [0.24, 0.59]; n=100 | — | 0.44 [0.27, 0.58]; n=130 | 0.70 [0.49, 0.90]; n=40 |
| Luna | 0.32 [0.15, 0.49]; n=100 | 0.50 [0.27, 0.69]; n=100 | 0.44 [0.27, 0.58]; n=130 | — | 0.54 [0.33, 0.72]; n=40 |
| DeepSeek | 0.60 [0.00, 1.00]; n=10 | 0.33 [—]; n=10 | 0.70 [0.49, 0.90]; n=40 | 0.54 [0.33, 0.72]; n=40 | — |

Coverage annotations: Opus: 0 partial, 1 not applicable; Sol: 0 partial, 1 not applicable; Sonnet: 7 partial, 28 not applicable; Luna: 0 partial, 0 not applicable; DeepSeek: 0 partial, 0 not applicable.

## readable-proof-simplification

[Library breakdowns](runs/file-quality-pilot-2026-10-21/reports/readable-proof-simplification-comparison.md)

### Library comparison

| Library | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Mathlib | — | — | 7/10<br>70.0% [39.7%, 89.2%] | 2/10<br>20.0% [5.7%, 51.0%] | 9/10<br>90.0% [59.6%, 98.2%] |
| Tau Ceti | — | — | 8/10<br>80.0% [49.0%, 94.3%] | 3/10<br>30.0% [10.8%, 60.3%] | 7/10<br>70.0% [39.7%, 89.2%] |
| Lean Pool | — | — | 9/10<br>90.0% [59.6%, 98.2%] | 6/10<br>60.0% [31.3%, 83.2%] | 9/10<br>90.0% [59.6%, 98.2%] |
| OpenAI Math | 84/100<br>84.0% [75.6%, 89.9%] | 82/100<br>82.0% [73.3%, 88.3%] | 78/100<br>78.0% [68.9%, 85.0%] | 25/100<br>25.0% [17.5%, 34.3%] | 7/10<br>70.0% [39.7%, 89.2%] |

### Model comparison

Full-pass reference: **130 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 100 | 1/1 | 100/100 | 84 | 84 | 84.0% [75.6%, 89.9%] | $34.58 / $44.96 |
| Sol | 100 | 1/1 | 100/100 | 82 | 82 | 82.0% [73.3%, 88.3%] | $12.68 / $16.48 |
| Sonnet | 130 | 1/1 | 130/130 | 102 | 102 | 78.5% [70.6%, 84.7%] | $18.52 / $18.52 |
| Luna | 130 | 1/1 | 130/130 | 36 | 36 | 27.7% [20.7%, 35.9%] | $0.50 / $0.50 |
| DeepSeek | 40 | 1/1 | 40/40 | 32 | 32 | 80.0% [65.2%, 89.5%] | $1.16 / $3.76 |

#### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | 0.65 [0.42, 0.83]; n=100 | 0.49 [0.27, 0.69]; n=100 | 0.19 [0.04, 0.30]; n=100 | 0.76 [—]; n=10 |
| Sol | 0.65 [0.42, 0.83]; n=100 | — | 0.38 [0.14, 0.59]; n=100 | 0.03 [-0.17, 0.20]; n=100 | 0.52 [—]; n=10 |
| Sonnet | 0.49 [0.27, 0.69]; n=100 | 0.38 [0.14, 0.59]; n=100 | — | 0.16 [0.01, 0.29]; n=130 | 0.78 [0.52, 1.00]; n=40 |
| Luna | 0.19 [0.04, 0.30]; n=100 | 0.03 [-0.17, 0.20]; n=100 | 0.16 [0.01, 0.29]; n=130 | — | 0.35 [0.21, 0.50]; n=40 |
| DeepSeek | 0.76 [—]; n=10 | 0.52 [—]; n=10 | 0.78 [0.52, 1.00]; n=40 | 0.35 [0.21, 0.50]; n=40 | — |

Coverage annotations: Opus: 0 partial, 1 not applicable; Sol: 0 partial, 1 not applicable; Sonnet: 0 partial, 1 not applicable; Luna: 0 partial, 1 not applicable; DeepSeek: 0 partial, 0 not applicable.
