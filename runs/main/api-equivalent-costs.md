# API-equivalent costs

Generated 2026-11-02T15:54:31+00:00 · [Methods and notation](../../AUDIT_METHODS.md).

Definition fidelity groups automatic missing-docstring flags with its Opus protocol; rule-only decisions cost $0. Repeated-machinery validation is a separate check, excluded from the original first-pass judgment and coverage counts.

| Audit | Model | Accepted judgments | Full-pass targets | API expenditure / full-pass estimate | USD / 1,000 judgments |
|---|---|---:|---:|---:|---:|
| unnecessary-hypotheses | Opus | 6600 | 5100 | $491.63 / $379.90 | $74.49 |
| unnecessary-hypotheses | Sol | 3100 | 5100 | $145.80 / $239.87 | $47.03 |
| unnecessary-hypotheses | Sonnet | 3600 | 5100 | $139.68 / $197.88 | $38.80 |
| unnecessary-hypotheses | Luna | 3100 | 5100 | $6.80 / $11.19 | $2.19 |
| unnecessary-hypotheses | DeepSeek | 600 | 5100 | $4.51 / $38.31 | $7.51 |
| duplicates-mathlib-inclusive | Opus | 4100 | 7000 | $222.89 / $380.55 | $54.36 |
| duplicates-mathlib-inclusive | Sol | 5100 | 7000 | $325.96 / $447.39 | $63.91 |
| duplicates-mathlib-inclusive | Sonnet | 7000 | 7000 | $183.17 / $183.17 | $26.17 |
| duplicates-mathlib-inclusive | Luna | 5100 | 7000 | $16.33 / $22.41 | $3.20 |
| duplicates-mathlib-inclusive | DeepSeek | 600 | 7000 | $2.26 / $26.42 | $3.77 |
| statement-generality | Opus | 100 | 130 | $31.36 / $40.77 | $313.62 |
| statement-generality | Sol | 100 | 130 | $13.16 / $17.11 | $131.61 |
| statement-generality | Sonnet | 130 | 130 | $15.59 / $15.59 | $119.95 |
| statement-generality | Luna | 130 | 130 | $0.60 / $0.60 | $4.64 |
| statement-generality | DeepSeek | 40 | 130 | $1.17 / $3.79 | $29.16 |
| vacuity-and-misstatement | Opus | 100 | 130 | $21.38 / $27.79 | $213.77 |
| vacuity-and-misstatement | Sol | 100 | 130 | $9.89 / $12.85 | $98.86 |
| vacuity-and-misstatement | Sonnet | 130 | 130 | $12.12 / $12.12 | $93.23 |
| vacuity-and-misstatement | Luna | 130 | 130 | $0.58 / $0.58 | $4.43 |
| vacuity-and-misstatement | DeepSeek | 40 | 130 | $1.15 / $3.73 | $28.70 |
| repeated-proof-machinery | Opus | 100 | 270 | $26.18 / $70.70 | $261.84 |
| repeated-proof-machinery | Sol | 100 | 270 | $8.15 / $22.02 | $81.55 |
| repeated-proof-machinery | Sonnet | 2604 | 270 | $223.53 / $23.18 | $85.84 |
| repeated-proof-machinery | Luna | 130 | 270 | $0.46 / $0.96 | $3.57 |
| repeated-proof-machinery | DeepSeek | 40 | 270 | $0.55 / $3.72 | $13.76 |
| readable-proof-simplification | Opus | 100 | 130 | $33.59 / $43.67 | $335.94 |
| readable-proof-simplification | Sol | 100 | 130 | $12.68 / $16.48 | $126.79 |
| readable-proof-simplification | Sonnet | 130 | 130 | $17.64 / $17.64 | $135.73 |
| readable-proof-simplification | Luna | 130 | 130 | $0.50 / $0.50 | $3.83 |
| readable-proof-simplification | DeepSeek | 40 | 130 | $1.16 / $3.76 | $28.89 |
| definition-fidelity | Opus | 5000 | 5000 | $336.14 / $336.14 | $67.23 |
| repeated-proof-machinery-validation | Sonnet | 180 | 180 | $17.81 / $17.81 | $98.94 |

## Appendix audits: not ready for use

[Assessment](../../AUDIT_APPENDIX.md). Excluded from the main report aggregates; their recorded expenditure remains part of the totals below.

| Audit | Model | Accepted judgments | Full-pass targets | API expenditure / full-pass estimate | USD / 1,000 judgments |
|---|---|---:|---:|---:|---:|
| concept-reinvention | Opus | 100 | 130 | $15.66 / $20.36 | $156.59 |
| concept-reinvention | Sol | 100 | 130 | $8.47 / $11.02 | $84.75 |
| concept-reinvention | Sonnet | 2231 | 130 | $152.59 / $8.89 | $68.40 |
| concept-reinvention | Luna | 130 | 130 | $0.65 / $0.65 | $5.04 |
| concept-reinvention | DeepSeek | 40 | 130 | $0.67 / $2.17 | $16.71 |
| simp-interface | Opus | 100 | 130 | $23.73 / $30.85 | $237.33 |
| simp-interface | Sol | 100 | 130 | $9.98 / $12.97 | $99.78 |
| simp-interface | Sonnet | 2226 | 130 | $219.71 / $12.83 | $98.70 |
| simp-interface | Luna | 130 | 130 | $0.59 / $0.59 | $4.57 |
| simp-interface | DeepSeek | 40 | 130 | $1.12 / $3.65 | $28.09 |

## Totals by model

| Model | API-equivalent USD |
|---|---:|
| Opus | $1202.57 |
| Sol | $534.09 |
| Sonnet | $981.85 |
| Luna | $26.52 |
| DeepSeek | $12.58 |
| **Total** | **$2757.62** |

## Rate sources

- [https://developers.openai.com/api/docs/pricing](https://developers.openai.com/api/docs/pricing)
- [https://platform.claude.com/docs/en/about-claude/pricing](https://platform.claude.com/docs/en/about-claude/pricing)

Frozen rates: `pricing/api-rates-2026-10-21.json`. Refresh with `python3 scripts/api_costs.py`. Mean-based projections include recorded retry expenditure and will change as more targets complete.
