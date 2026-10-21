# API-equivalent costs

Generated 2026-10-21T07:24:44+00:00 · [Methods and notation](../../AUDIT_METHODS.md).

| Audit | Model | Accepted judgments | Full-pass targets | API expenditure / full-pass estimate | USD / 1,000 judgments |
|---|---|---:|---:|---:|---:|
| unnecessary-hypotheses | Opus | 3520 | 2000 | $255.80 / $145.34 | $72.67 |
| unnecessary-hypotheses | Sol | 3016 | 2000 | $141.45 / $93.80 | $46.90 |
| unnecessary-hypotheses | Sonnet | 3029 | 2000 | $106.56 / $70.36 | $35.18 |
| unnecessary-hypotheses | Luna | 3026 | 2000 | $6.56 / $4.34 | $2.17 |
| unnecessary-hypotheses | DeepSeek | 1 | 2000 | $0.01 / $13.87 | $6.93 |
| duplicates-mathlib-inclusive | Opus | 4020 | 5000 | $217.66 / $270.72 | $54.14 |
| duplicates-mathlib-inclusive | Sol | 5016 | 5000 | $320.53 / $319.51 | $63.90 |
| duplicates-mathlib-inclusive | Sonnet | 5029 | 5000 | $125.94 / $125.21 | $25.04 |
| duplicates-mathlib-inclusive | Luna | 5026 | 5000 | $16.08 / $16.00 | $3.20 |
| duplicates-mathlib-inclusive | DeepSeek | 0 | 5000 | $0.00 / — | $0.00 |
| concept-reinvention | Opus | 20 | 30 | $2.85 / $4.28 | $142.59 |
| concept-reinvention | Sol | 16 | 30 | $1.50 / $2.81 | $93.52 |
| concept-reinvention | Sonnet | 59 | 30 | $4.49 / $2.28 | $76.03 |
| concept-reinvention | Luna | 56 | 30 | $0.29 / $0.16 | $5.23 |
| concept-reinvention | DeepSeek | 0 | 30 | $0.00 / — | $0.00 |
| statement-generality | Opus | 19 | 30 | $6.75 / $10.66 | $355.29 |
| statement-generality | Sol | 16 | 30 | $2.26 / $4.23 | $140.96 |
| statement-generality | Sonnet | 59 | 30 | $6.91 / $3.51 | $117.06 |
| statement-generality | Luna | 56 | 30 | $0.27 / $0.14 | $4.80 |
| statement-generality | DeepSeek | 0 | 30 | $0.00 / — | $0.00 |
| vacuity-and-misstatement | Opus | 19 | 30 | $4.28 / $6.76 | $225.42 |
| vacuity-and-misstatement | Sol | 15 | 30 | $1.35 / $2.69 | $89.72 |
| vacuity-and-misstatement | Sonnet | 59 | 30 | $5.11 / $2.60 | $86.69 |
| vacuity-and-misstatement | Luna | 56 | 30 | $0.26 / $0.14 | $4.69 |
| vacuity-and-misstatement | DeepSeek | 0 | 30 | $0.00 / — | $0.00 |
| simp-interface | Opus | 19 | 30 | $5.49 / $8.66 | $288.80 |
| simp-interface | Sol | 15 | 30 | $1.51 / $3.03 | $100.87 |
| simp-interface | Sonnet | 58 | 30 | $5.12 / $2.65 | $88.27 |
| simp-interface | Luna | 55 | 30 | $0.26 / $0.14 | $4.71 |
| simp-interface | DeepSeek | 0 | 30 | $0.00 / — | $0.00 |
| repeated-proof-machinery | Opus | 19 | 30 | $4.42 / $6.98 | $232.54 |
| repeated-proof-machinery | Sol | 15 | 30 | $1.27 / $2.54 | $84.61 |
| repeated-proof-machinery | Sonnet | 58 | 30 | $4.35 / $2.25 | $75.04 |
| repeated-proof-machinery | Luna | 55 | 30 | $0.20 / $0.11 | $3.62 |
| repeated-proof-machinery | DeepSeek | 0 | 30 | $0.00 / — | $0.00 |
| readable-proof-simplification | Opus | 19 | 30 | $6.06 / $9.56 | $318.73 |
| readable-proof-simplification | Sol | 14 | 30 | $1.68 / $3.61 | $120.31 |
| readable-proof-simplification | Sonnet | 58 | 30 | $7.41 / $3.83 | $127.83 |
| readable-proof-simplification | Luna | 55 | 30 | $0.21 / $0.12 | $3.89 |
| readable-proof-simplification | DeepSeek | 0 | 30 | $0.00 / — | $0.00 |

## Totals by model

| Model | API-equivalent USD |
|---|---:|
| Opus | $503.31 |
| Sol | $471.55 |
| Sonnet | $265.89 |
| Luna | $24.14 |
| DeepSeek | $0.01 |
| **Total** | **$1264.89** |

## Rate sources

- [https://developers.openai.com/api/docs/pricing](https://developers.openai.com/api/docs/pricing)
- [https://platform.claude.com/docs/en/about-claude/pricing](https://platform.claude.com/docs/en/about-claude/pricing)

Frozen rates: `pricing/api-rates-2026-10-21.json`. Refresh with `python3 scripts/api_costs.py`. Mean-based projections include recorded retry expenditure and will change as more targets complete.
