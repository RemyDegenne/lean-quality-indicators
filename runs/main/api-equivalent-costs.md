# API-equivalent costs

Generated 2026-10-22T01:15:15+00:00 · [Methods and notation](../../AUDIT_METHODS.md).

| Audit | Model | Accepted judgments | Full-pass targets | API expenditure / full-pass estimate | USD / 1,000 judgments |
|---|---|---:|---:|---:|---:|
| unnecessary-hypotheses | Opus | 3600 | 2100 | $264.19 / $154.11 | $73.39 |
| unnecessary-hypotheses | Sol | 3100 | 2100 | $145.80 / $98.77 | $47.03 |
| unnecessary-hypotheses | Sonnet | 3100 | 2100 | $110.14 / $74.61 | $35.53 |
| unnecessary-hypotheses | Luna | 3100 | 2100 | $6.81 / $4.61 | $2.20 |
| unnecessary-hypotheses | DeepSeek | 60 | 2100 | $0.57 / $20.12 | $9.58 |
| duplicates-mathlib-inclusive | Opus | 4100 | 5100 | $222.89 / $277.26 | $54.36 |
| duplicates-mathlib-inclusive | Sol | 5100 | 5100 | $325.96 / $325.96 | $63.91 |
| duplicates-mathlib-inclusive | Sonnet | 5100 | 5100 | $128.13 / $128.13 | $25.12 |
| duplicates-mathlib-inclusive | Luna | 5100 | 5100 | $16.33 / $16.33 | $3.20 |
| duplicates-mathlib-inclusive | DeepSeek | 60 | 5100 | $0.19 / $16.25 | $3.19 |
| concept-reinvention | Opus | 100 | 130 | $15.66 / $20.36 | $156.59 |
| concept-reinvention | Sol | 100 | 130 | $8.47 / $11.02 | $84.75 |
| concept-reinvention | Sonnet | 130 | 130 | $8.99 / $8.99 | $69.14 |
| concept-reinvention | Luna | 130 | 130 | $0.65 / $0.65 | $5.04 |
| concept-reinvention | DeepSeek | 40 | 130 | $0.67 / $2.17 | $16.71 |
| statement-generality | Opus | 100 | 130 | $32.26 / $41.93 | $322.57 |
| statement-generality | Sol | 100 | 130 | $13.16 / $17.11 | $131.61 |
| statement-generality | Sonnet | 130 | 130 | $16.38 / $16.38 | $125.96 |
| statement-generality | Luna | 130 | 130 | $0.63 / $0.63 | $4.83 |
| statement-generality | DeepSeek | 39 | 130 | $1.16 / $3.86 | $29.69 |
| vacuity-and-misstatement | Opus | 100 | 130 | $21.38 / $27.79 | $213.77 |
| vacuity-and-misstatement | Sol | 100 | 130 | $9.89 / $12.85 | $98.86 |
| vacuity-and-misstatement | Sonnet | 130 | 130 | $12.33 / $12.33 | $94.88 |
| vacuity-and-misstatement | Luna | 130 | 130 | $0.58 / $0.58 | $4.49 |
| vacuity-and-misstatement | DeepSeek | 40 | 130 | $1.15 / $3.73 | $28.70 |
| simp-interface | Opus | 100 | 130 | $24.70 / $32.11 | $246.97 |
| simp-interface | Sol | 100 | 130 | $9.98 / $12.97 | $99.78 |
| simp-interface | Sonnet | 130 | 130 | $12.54 / $12.54 | $96.42 |
| simp-interface | Luna | 130 | 130 | $0.59 / $0.59 | $4.57 |
| simp-interface | DeepSeek | 38 | 130 | $1.09 / $3.73 | $28.66 |
| repeated-proof-machinery | Opus | 100 | 130 | $26.18 / $34.04 | $261.84 |
| repeated-proof-machinery | Sol | 100 | 130 | $8.15 / $10.60 | $81.55 |
| repeated-proof-machinery | Sonnet | 130 | 130 | $11.00 / $11.00 | $84.65 |
| repeated-proof-machinery | Luna | 130 | 130 | $0.46 / $0.46 | $3.57 |
| repeated-proof-machinery | DeepSeek | 38 | 130 | $0.53 / $1.81 | $13.90 |
| readable-proof-simplification | Opus | 100 | 130 | $34.58 / $44.96 | $345.81 |
| readable-proof-simplification | Sol | 100 | 130 | $12.68 / $16.48 | $126.79 |
| readable-proof-simplification | Sonnet | 130 | 130 | $18.52 / $18.52 | $142.44 |
| readable-proof-simplification | Luna | 130 | 130 | $0.50 / $0.50 | $3.86 |
| readable-proof-simplification | DeepSeek | 36 | 130 | $1.04 / $3.77 | $28.96 |

## Totals by model

| Model | API-equivalent USD |
|---|---:|
| Opus | $641.84 |
| Sol | $534.09 |
| Sonnet | $318.02 |
| Luna | $26.56 |
| DeepSeek | $6.40 |
| **Total** | **$1526.91** |

## Rate sources

- [https://developers.openai.com/api/docs/pricing](https://developers.openai.com/api/docs/pricing)
- [https://platform.claude.com/docs/en/about-claude/pricing](https://platform.claude.com/docs/en/about-claude/pricing)

Frozen rates: `pricing/api-rates-2026-10-21.json`. Refresh with `python3 scripts/api_costs.py`. Mean-based projections include recorded retry expenditure and will change as more targets complete.
