# API-equivalent costs

Generated 2026-10-27T17:31:05+00:00 · [Methods and notation](../../AUDIT_METHODS.md).

Definition fidelity groups automatic missing-docstring flags with its Opus protocol; rule-only decisions cost $0. Repeated-machinery validation is a separate check, excluded from the original first-pass judgment and coverage counts.

| Audit | Model | Accepted judgments | Full-pass targets | API expenditure / full-pass estimate | USD / 1,000 judgments |
|---|---|---:|---:|---:|---:|
| unnecessary-hypotheses | Opus | 6600 | 5100 | $491.63 / $379.90 | $74.49 |
| unnecessary-hypotheses | Sol | 3100 | 5100 | $145.80 / $239.87 | $47.03 |
| unnecessary-hypotheses | Sonnet | 3168 | 5100 | $114.78 / $184.78 | $36.23 |
| unnecessary-hypotheses | Luna | 3100 | 5100 | $6.81 / $11.20 | $2.20 |
| unnecessary-hypotheses | DeepSeek | 600 | 5100 | $4.52 / $38.46 | $7.54 |
| duplicates-mathlib-inclusive | Opus | 4100 | 5100 | $222.89 / $277.26 | $54.36 |
| duplicates-mathlib-inclusive | Sol | 5100 | 5100 | $325.96 / $325.96 | $63.91 |
| duplicates-mathlib-inclusive | Sonnet | 5168 | 5100 | $129.51 / $127.80 | $25.06 |
| duplicates-mathlib-inclusive | Luna | 5100 | 5100 | $16.33 / $16.33 | $3.20 |
| duplicates-mathlib-inclusive | DeepSeek | 600 | 5100 | $2.26 / $19.25 | $3.77 |
| statement-generality | Opus | 100 | 130 | $32.26 / $41.93 | $322.57 |
| statement-generality | Sol | 100 | 130 | $13.16 / $17.11 | $131.61 |
| statement-generality | Sonnet | 130 | 130 | $16.38 / $16.38 | $125.96 |
| statement-generality | Luna | 130 | 130 | $0.63 / $0.63 | $4.83 |
| statement-generality | DeepSeek | 40 | 130 | $1.17 / $3.79 | $29.16 |
| vacuity-and-misstatement | Opus | 100 | 130 | $21.38 / $27.79 | $213.77 |
| vacuity-and-misstatement | Sol | 100 | 130 | $9.89 / $12.85 | $98.86 |
| vacuity-and-misstatement | Sonnet | 130 | 130 | $12.33 / $12.33 | $94.88 |
| vacuity-and-misstatement | Luna | 130 | 130 | $0.58 / $0.58 | $4.49 |
| vacuity-and-misstatement | DeepSeek | 40 | 130 | $1.15 / $3.73 | $28.70 |
| repeated-proof-machinery | Opus | 100 | 130 | $26.18 / $34.04 | $261.84 |
| repeated-proof-machinery | Sol | 100 | 130 | $8.15 / $10.60 | $81.55 |
| repeated-proof-machinery | Sonnet | 2311 | 130 | $193.61 / $10.89 | $83.78 |
| repeated-proof-machinery | Luna | 130 | 130 | $0.46 / $0.46 | $3.57 |
| repeated-proof-machinery | DeepSeek | 40 | 130 | $0.55 / $1.79 | $13.76 |
| readable-proof-simplification | Opus | 100 | 130 | $34.58 / $44.96 | $345.81 |
| readable-proof-simplification | Sol | 100 | 130 | $12.68 / $16.48 | $126.79 |
| readable-proof-simplification | Sonnet | 130 | 130 | $18.52 / $18.52 | $142.44 |
| readable-proof-simplification | Luna | 130 | 130 | $0.50 / $0.50 | $3.86 |
| readable-proof-simplification | DeepSeek | 40 | 130 | $1.16 / $3.76 | $28.89 |
| definition-fidelity | Opus | 5000 | 5000 | $336.14 / $336.14 | $67.23 |
| repeated-proof-machinery-validation | Sonnet | 180 | 180 | $19.61 / $19.61 | $108.95 |

## Appendix audits: not ready for use

[Assessment](../../AUDIT_APPENDIX.md). Excluded from the main report aggregates; their recorded expenditure remains part of the totals below.

| Audit | Model | Accepted judgments | Full-pass targets | API expenditure / full-pass estimate | USD / 1,000 judgments |
|---|---|---:|---:|---:|---:|
| concept-reinvention | Opus | 100 | 130 | $15.66 / $20.36 | $156.59 |
| concept-reinvention | Sol | 100 | 130 | $8.47 / $11.02 | $84.75 |
| concept-reinvention | Sonnet | 2231 | 130 | $155.15 / $9.04 | $69.54 |
| concept-reinvention | Luna | 130 | 130 | $0.65 / $0.65 | $5.04 |
| concept-reinvention | DeepSeek | 40 | 130 | $0.67 / $2.17 | $16.71 |
| simp-interface | Opus | 100 | 130 | $24.70 / $32.11 | $246.97 |
| simp-interface | Sol | 100 | 130 | $9.98 / $12.97 | $99.78 |
| simp-interface | Sonnet | 2226 | 130 | $229.55 / $13.41 | $103.12 |
| simp-interface | Luna | 130 | 130 | $0.59 / $0.59 | $4.57 |
| simp-interface | DeepSeek | 40 | 130 | $1.12 / $3.65 | $28.09 |

## Totals by model

| Model | API-equivalent USD |
|---|---:|
| Opus | $1205.42 |
| Sol | $534.09 |
| Sonnet | $889.45 |
| Luna | $26.56 |
| DeepSeek | $12.60 |
| **Total** | **$2668.12** |

## Rate sources

- [https://developers.openai.com/api/docs/pricing](https://developers.openai.com/api/docs/pricing)
- [https://platform.claude.com/docs/en/about-claude/pricing](https://platform.claude.com/docs/en/about-claude/pricing)

Frozen rates: `pricing/api-rates-2026-10-21.json`. Refresh with `python3 scripts/api_costs.py`. Mean-based projections include recorded retry expenditure and will change as more targets complete.
