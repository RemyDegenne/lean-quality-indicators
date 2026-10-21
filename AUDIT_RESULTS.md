# Audit results

Generated 2026-10-21T05:27:13+00:00 · [Methods and notation](AUDIT_METHODS.md) · [Cost summary](runs/main/api-equivalent-costs.md).

All eight audits, each combining its libraries.

## unnecessary-hypotheses

[Library breakdowns](runs/main/unnecessary-hypotheses/audit-comparison.md)

Full-pass reference: **2000 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 2000 | 2/2 | 3500/3500 | 348 | 205 | 9.9% [8.7%, 11.3%] | $254.27 / $145.30 |
| Sol | 1500 | 2/2 | 3000/3000 | 374 | 189 | 12.5% [10.9%, 14.2%] | $140.71 / $93.81 |
| Sonnet | 1500 | 2/2 | 3000/3000 | 245 | 137 | 8.1% [6.8%, 9.6%] | $105.40 / $70.27 |
| Luna | 1500 | 2/2 | 3000/3000 | 310 | 193 | 10.3% [8.9%, 12.0%] | $6.51 / $4.34 |
| GLM | 50 | 0/1 | 6/50 | 1 | 1 | 16.7% [3.0%, 56.4%] | $0.77 / $256.50 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | GLM |
|---|---:|---:|---:|---:|---:|
| Opus | 0.92 [0.89, 0.95]; n=1500 | 0.91 [0.87, 0.94]; n=1500 | 0.85 [0.80, 0.89]; n=1500 | 0.73 [0.67, 0.78]; n=1500 | 1.00 [—]; n=6 |
| Sol | 0.91 [0.87, 0.94]; n=1500 | 0.99 [0.97, 1.00]; n=1500 | 0.78 [0.73, 0.82]; n=1500 | 0.70 [0.64, 0.76]; n=1500 | 1.00 [—]; n=6 |
| Sonnet | 0.85 [0.80, 0.89]; n=1500 | 0.78 [0.73, 0.82]; n=1500 | 0.87 [0.82, 0.91]; n=1500 | 0.70 [0.64, 0.76]; n=1500 | 1.00 [—]; n=6 |
| Luna | 0.73 [0.67, 0.78]; n=1500 | 0.70 [0.64, 0.76]; n=1500 | 0.70 [0.64, 0.76]; n=1500 | 0.73 [0.67, 0.78]; n=1500 | 1.00 [—]; n=6 |
| GLM | 1.00 [—]; n=6 | 1.00 [—]; n=6 | 1.00 [—]; n=6 | 1.00 [—]; n=6 | — |

## duplicates-mathlib-inclusive

[Library breakdowns](runs/main/duplicates-mathlib-inclusive/audit-comparison.md)

Opus uses the earlier prompt on four libraries, without Mathlib targets.

Full-pass reference: **5000 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 4000 | 1/1 | 4000/4000 | 301 | 301 | 7.5% [6.7%, 8.4%] | $216.29 / $270.36 |
| Sol | 5000 | 1/1 | 5000/5000 | 1447 | 1447 | 28.9% [27.7%, 30.2%] | $319.51 / $319.51 |
| Sonnet | 5000 | 1/1 | 5000/5000 | 519 | 519 | 10.4% [9.6%, 11.3%] | $124.97 / $124.97 |
| Luna | 5000 | 1/1 | 5000/5000 | 1352 | 1352 | 27.0% [25.8%, 28.3%] | $16.00 / $16.00 |
| GLM | 50 | 0/1 | 6/50 | 3 | 3 | 50.0% [18.8%, 81.2%] | $0.18 / $150.98 |

### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | GLM |
|---|---:|---:|---:|---:|---:|
| Opus | — | 0.57 [0.54, 0.60]; n=4000 | 0.74 [0.70, 0.78]; n=4000 | 0.54 [0.51, 0.57]; n=4000 | —; n=4 |
| Sol | 0.57 [0.54, 0.60]; n=4000 | — | 0.48 [0.46, 0.51]; n=5000 | 0.69 [0.67, 0.71]; n=5000 | 0.71 [0.71, 0.71]; n=6 |
| Sonnet | 0.74 [0.70, 0.78]; n=4000 | 0.48 [0.46, 0.51]; n=5000 | — | 0.50 [0.47, 0.53]; n=5000 | 0.45 [—]; n=6 |
| Luna | 0.54 [0.51, 0.57]; n=4000 | 0.69 [0.67, 0.71]; n=5000 | 0.50 [0.47, 0.53]; n=5000 | — | 0.71 [0.71, 0.71]; n=6 |
| GLM | —; n=4 | 0.71 [0.71, 0.71]; n=6 | 0.45 [—]; n=6 | 0.71 [0.71, 0.71]; n=6 | — |

## concept-reinvention

[Library breakdowns](runs/file-quality-pilot-2026-10-21/reports/concept-reinvention-comparison.md)

Full-pass reference: **30 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Sonnet | 30 | 1/1 | 30/30 | 6 | 6 | 20.0% [9.5%, 37.3%] | $2.19 / $2.19 |
| Luna | 30 | 0/1 | 24/30 | 0 | 0 | 0.0% [0.0%, 13.8%] | $0.13 / $0.16 |
| GLM | 30 | 0/1 | 0/30 | 0 | 0 | — | $0.00 / — |

### Correlation matrix

| Model | Sonnet | Luna | GLM |
|---|---:|---:|---:|
| Sonnet | — | —; n=24 | — |
| Luna | —; n=24 | — | — |
| GLM | — | — | — |

Coverage annotations: Sonnet: 0 partial, 5 not applicable; Luna: 0 partial, 0 not applicable; GLM: 0 partial, 0 not applicable.

## statement-generality

[Library breakdowns](runs/file-quality-pilot-2026-10-21/reports/statement-generality-comparison.md)

Full-pass reference: **30 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Sonnet | 30 | 1/1 | 30/30 | 18 | 18 | 60.0% [42.3%, 75.4%] | $3.07 / $3.07 |
| Luna | 30 | 0/1 | 25/30 | 9 | 9 | 36.0% [20.2%, 55.5%] | $0.12 / $0.15 |
| GLM | 30 | 0/1 | 0/30 | 0 | 0 | — | $0.00 / — |

### Correlation matrix

| Model | Sonnet | Luna | GLM |
|---|---:|---:|---:|
| Sonnet | — | 0.27 [-0.04, 0.60]; n=25 | — |
| Luna | 0.27 [-0.04, 0.60]; n=25 | — | — |
| GLM | — | — | — |

Coverage annotations: Sonnet: 0 partial, 0 not applicable; Luna: 0 partial, 0 not applicable; GLM: 0 partial, 0 not applicable.

## vacuity-and-misstatement

[Library breakdowns](runs/file-quality-pilot-2026-10-21/reports/vacuity-and-misstatement-comparison.md)

Full-pass reference: **30 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Sonnet | 30 | 1/1 | 30/30 | 5 | 5 | 16.7% [7.3%, 33.6%] | $2.24 / $2.24 |
| Luna | 30 | 0/1 | 24/30 | 2 | 2 | 8.3% [2.3%, 25.8%] | $0.11 / $0.14 |
| GLM | 30 | 0/1 | 0/30 | 0 | 0 | — | $0.00 / — |

### Correlation matrix

| Model | Sonnet | Luna | GLM |
|---|---:|---:|---:|
| Sonnet | — | -0.13 [—]; n=24 | — |
| Luna | -0.13 [—]; n=24 | — | — |
| GLM | — | — | — |

Coverage annotations: Sonnet: 0 partial, 0 not applicable; Luna: 0 partial, 0 not applicable; GLM: 0 partial, 0 not applicable.

## simp-interface

[Library breakdowns](runs/file-quality-pilot-2026-10-21/reports/simp-interface-comparison.md)

Full-pass reference: **30 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Sonnet | 30 | 1/1 | 30/30 | 13 | 13 | 43.3% [27.4%, 60.8%] | $2.39 / $2.39 |
| Luna | 30 | 0/1 | 24/30 | 9 | 9 | 37.5% [21.2%, 57.3%] | $0.13 / $0.16 |
| GLM | 30 | 0/1 | 0/30 | 0 | 0 | — | $0.00 / — |

### Correlation matrix

| Model | Sonnet | Luna | GLM |
|---|---:|---:|---:|
| Sonnet | — | 0.57 [0.24, 0.90]; n=24 | — |
| Luna | 0.57 [0.24, 0.90]; n=24 | — | — |
| GLM | — | — | — |

Coverage annotations: Sonnet: 0 partial, 1 not applicable; Luna: 0 partial, 0 not applicable; GLM: 0 partial, 0 not applicable.

## repeated-proof-machinery

[Library breakdowns](runs/file-quality-pilot-2026-10-21/reports/repeated-proof-machinery-comparison.md)

Full-pass reference: **30 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Sonnet | 30 | 1/1 | 30/30 | 10 | 10 | 33.3% [19.2%, 51.2%] | $2.06 / $2.06 |
| Luna | 30 | 0/1 | 24/30 | 5 | 5 | 20.8% [9.2%, 40.5%] | $0.09 / $0.11 |
| GLM | 30 | 0/1 | 0/30 | 0 | 0 | — | $0.00 / — |

### Correlation matrix

| Model | Sonnet | Luna | GLM |
|---|---:|---:|---:|
| Sonnet | — | 0.61 [0.36, 0.84]; n=24 | — |
| Luna | 0.61 [0.36, 0.84]; n=24 | — | — |
| GLM | — | — | — |

Coverage annotations: Sonnet: 0 partial, 1 not applicable; Luna: 0 partial, 0 not applicable; GLM: 0 partial, 0 not applicable.

## readable-proof-simplification

[Library breakdowns](runs/file-quality-pilot-2026-10-21/reports/readable-proof-simplification-comparison.md)

Full-pass reference: **30 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Sonnet | 30 | 1/1 | 30/30 | 24 | 24 | 80.0% [62.7%, 90.5%] | $3.52 / $3.52 |
| Luna | 30 | 0/1 | 24/30 | 9 | 9 | 37.5% [21.2%, 57.3%] | $0.10 / $0.12 |
| GLM | 30 | 0/1 | 0/30 | 0 | 0 | — | $0.00 / — |

### Correlation matrix

| Model | Sonnet | Luna | GLM |
|---|---:|---:|---:|
| Sonnet | — | 0.40 [0.19, 0.61]; n=24 | — |
| Luna | 0.40 [0.19, 0.61]; n=24 | — | — |
| GLM | — | — | — |

Coverage annotations: Sonnet: 0 partial, 0 not applicable; Luna: 0 partial, 0 not applicable; GLM: 0 partial, 0 not applicable.
