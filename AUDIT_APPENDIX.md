# Appendix: audits not ready for use

**Concept reinvention and simp interface are not ready for use in library comparisons.** Their judgments and protocols are retained for investigation, but excluded from the [main reports](AUDIT_RESULTS.md), combined flag rates, correlations and summary expenditure. The [cost ledger](runs/main/api-equivalent-costs.md) retains their expenditure separately.

The [60-target source review](runs/library-quality-scale-2026-10-26/sample-review-2026-10-27.json) records the assessment behind this placement. It sampled 20 targets per audit across six libraries, including 14 flagged and six unflagged targets. It was a static source review, without compiling replacements; this positive-enriched sample does not estimate defect prevalence.

## concept-reinvention

[Library breakdowns](runs/file-quality-pilot-2026-10-21/reports/concept-reinvention-comparison.md)

Source review found permitted wrappers and deliberate representations flagged, along with internal-project duplication outside the rubric's Mathlib scope.

### Library comparison

| Library | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Mathlib | — | — | 28/372<br>7.5% [5.3%, 10.7%] | 0/10<br>0.0% [0.0%, 27.8%] | 3/10<br>30.0% [10.8%, 60.3%] |
| Tau Ceti | — | — | 9/372<br>2.4% [1.3%, 4.5%] | 0/10<br>0.0% [0.0%, 27.8%] | 0/10<br>0.0% [0.0%, 27.8%] |
| Formal Frontier | — | — | 30/372<br>8.1% [5.7%, 11.3%] | — | — |
| Lean Pool | — | — | 52/371<br>14.0% [10.9%, 17.9%] | 0/10<br>0.0% [0.0%, 27.8%] | 5/10<br>50.0% [23.7%, 76.3%] |
| FLT (Anthropic) | — | — | 56/372<br>15.1% [11.8%, 19.0%] | — | — |
| OpenAI Math | 7/100<br>7.0% [3.4%, 13.7%] | 1/100<br>1.0% [0.2%, 5.4%] | 25/372<br>6.7% [4.6%, 9.7%] | 5/100<br>5.0% [2.2%, 11.2%] | 2/10<br>20.0% [5.7%, 51.0%] |

### Model comparison

Full-pass reference: **130 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 100 | 1/1 | 100/100 | 7 | 7 | 7.0% [3.4%, 13.7%] | $15.66 / $20.36 |
| Sol | 100 | 1/1 | 100/100 | 1 | 1 | 1.0% [0.2%, 5.4%] | $8.47 / $11.02 |
| Sonnet | 3000 | 0/1 | 2231/3000 | 200 | 200 | 9.0% [7.8%, 10.2%] | $155.15 / $9.04 |
| Luna | 130 | 1/1 | 130/130 | 5 | 5 | 3.8% [1.7%, 8.7%] | $0.65 / $0.65 |
| DeepSeek | 40 | 1/1 | 40/40 | 10 | 10 | 25.0% [14.2%, 40.2%] | $0.67 / $2.17 |

#### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | 0.37 [—]; n=100 | 0.59 [0.22, 0.88]; n=100 | 0.12 [-0.08, 0.45]; n=100 | 1.00 [—]; n=10 |
| Sol | 0.37 [—]; n=100 | — | 0.40 [—]; n=100 | 0.44 [—]; n=100 | 0.67 [—]; n=10 |
| Sonnet | 0.59 [0.22, 0.88]; n=100 | 0.40 [—]; n=100 | — | 0.07 [-0.08, 0.33]; n=130 | 0.72 [0.46, 0.94]; n=40 |
| Luna | 0.12 [-0.08, 0.45]; n=100 | 0.44 [—]; n=100 | 0.07 [-0.08, 0.33]; n=130 | — | 0.28 [—]; n=40 |
| DeepSeek | 1.00 [—]; n=10 | 0.67 [—]; n=10 | 0.72 [0.46, 0.94]; n=40 | 0.28 [—]; n=40 | — |

Coverage annotations: Opus: 0 partial, 49 not applicable; Sol: 0 partial, 22 not applicable; Sonnet: 2 partial, 642 not applicable; Luna: 0 partial, 1 not applicable; DeepSeek: 0 partial, 3 not applicable.

## simp-interface

[Library breakdowns](runs/file-quality-pilot-2026-10-21/reports/simp-interface-comparison.md)

Source review found useful API additions mixed with objections to harmless overlapping rules and claims lacking a demonstrated simplification problem.

### Library comparison

| Library | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Mathlib | — | — | 170/372<br>45.7% [40.7%, 50.8%] | 4/10<br>40.0% [16.8%, 68.7%] | 7/10<br>70.0% [39.7%, 89.2%] |
| Tau Ceti | — | — | 165/372<br>44.4% [39.4%, 49.4%] | 1/10<br>10.0% [1.8%, 40.4%] | 3/10<br>30.0% [10.8%, 60.3%] |
| Formal Frontier | — | — | 200/370<br>54.1% [49.0%, 59.1%] | — | — |
| Lean Pool | — | — | 226/371<br>60.9% [55.9%, 65.7%] | 6/10<br>60.0% [31.3%, 83.2%] | 9/10<br>90.0% [59.6%, 98.2%] |
| FLT (Anthropic) | — | — | 168/370<br>45.4% [40.4%, 50.5%] | — | — |
| OpenAI Math | 45/100<br>45.0% [35.6%, 54.8%] | 31/100<br>31.0% [22.8%, 40.6%] | 211/371<br>56.9% [51.8%, 61.8%] | 29/100<br>29.0% [21.0%, 38.5%] | 9/10<br>90.0% [59.6%, 98.2%] |

### Model comparison

Full-pass reference: **130 targets**.

| Model | Selected targets | Passes done/planned | Judgments done/planned | Flagged judgments | Distinct targets flagged | First-pass rate (95% CI) | API expenditure / full-pass estimate |
|---|---:|---:|---:|---:|---:|---:|---:|
| Opus | 100 | 1/1 | 100/100 | 45 | 45 | 45.0% [35.6%, 54.8%] | $24.70 / $32.11 |
| Sol | 100 | 1/1 | 100/100 | 31 | 31 | 31.0% [22.8%, 40.6%] | $9.98 / $12.97 |
| Sonnet | 3000 | 0/1 | 2226/3000 | 1140 | 1140 | 51.2% [49.1%, 53.3%] | $229.55 / $13.41 |
| Luna | 130 | 1/1 | 130/130 | 40 | 40 | 30.8% [23.5%, 39.2%] | $0.59 / $0.59 |
| DeepSeek | 40 | 1/1 | 40/40 | 28 | 28 | 70.0% [54.6%, 81.9%] | $1.12 / $3.65 |

#### Correlation matrix

| Model | Opus | Sol | Sonnet | Luna | DeepSeek |
|---|---:|---:|---:|---:|---:|
| Opus | — | 0.57 [0.39, 0.71]; n=100 | 0.58 [0.41, 0.71]; n=100 | 0.40 [0.21, 0.56]; n=100 | 0.51 [—]; n=10 |
| Sol | 0.57 [0.39, 0.71]; n=100 | — | 0.56 [0.44, 0.69]; n=100 | 0.52 [0.34, 0.70]; n=100 | 0.22 [—]; n=10 |
| Sonnet | 0.58 [0.41, 0.71]; n=100 | 0.56 [0.44, 0.69]; n=100 | — | 0.30 [0.15, 0.46]; n=130 | 0.55 [0.30, 0.77]; n=40 |
| Luna | 0.40 [0.21, 0.56]; n=100 | 0.52 [0.34, 0.70]; n=100 | 0.30 [0.15, 0.46]; n=130 | — | 0.28 [0.00, 0.53]; n=40 |
| DeepSeek | 0.51 [—]; n=10 | 0.22 [—]; n=10 | 0.55 [0.30, 0.77]; n=40 | 0.28 [0.00, 0.53]; n=40 | — |

Coverage annotations: Opus: 0 partial, 19 not applicable; Sol: 0 partial, 0 not applicable; Sonnet: 7 partial, 158 not applicable; Luna: 0 partial, 1 not applicable; DeepSeek: 0 partial, 1 not applicable.
