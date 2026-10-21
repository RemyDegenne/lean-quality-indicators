# API-equivalent costs

Generated 2026-10-21T11:05:07+00:00 · [Methods and notation](../../AUDIT_METHODS.md).

| Audit | Model | Accepted judgments | Full-pass targets | API expenditure / full-pass estimate | USD / 1,000 judgments |
|---|---|---:|---:|---:|---:|
| unnecessary-hypotheses | Opus | 3522 | 2000 | $256.57 / $145.70 | $72.85 |
| unnecessary-hypotheses | Sol | 3070 | 2000 | $144.28 / $94.00 | $47.00 |
| unnecessary-hypotheses | Sonnet | 3041 | 2000 | $107.41 / $70.64 | $35.32 |
| unnecessary-hypotheses | Luna | 3048 | 2000 | $6.64 / $4.36 | $2.18 |
| unnecessary-hypotheses | DeepSeek | 1 | 2000 | $0.01 / $26.51 | $13.26 |
| duplicates-mathlib-inclusive | Opus | 4022 | 5000 | $217.81 / $270.77 | $54.15 |
| duplicates-mathlib-inclusive | Sol | 5070 | 5000 | $324.01 / $319.54 | $63.91 |
| duplicates-mathlib-inclusive | Sonnet | 5041 | 5000 | $126.30 / $125.28 | $25.06 |
| duplicates-mathlib-inclusive | Luna | 5048 | 5000 | $16.16 / $16.00 | $3.20 |
| duplicates-mathlib-inclusive | DeepSeek | 0 | 5000 | $0.00 / — | $0.00 |
| concept-reinvention | Opus | 22 | 30 | $3.37 / $4.60 | $153.21 |
| concept-reinvention | Sol | 70 | 30 | $6.15 / $2.64 | $87.88 |
| concept-reinvention | Sonnet | 70 | 30 | $4.98 / $2.14 | $71.20 |
| concept-reinvention | Luna | 78 | 30 | $0.40 / $0.15 | $5.10 |
| concept-reinvention | DeepSeek | 0 | 30 | $0.00 / — | $0.00 |
| statement-generality | Opus | 22 | 30 | $7.60 / $10.37 | $345.64 |
| statement-generality | Sol | 70 | 30 | $9.35 / $4.01 | $133.53 |
| statement-generality | Sonnet | 70 | 30 | $7.96 / $3.41 | $113.77 |
| statement-generality | Luna | 78 | 30 | $0.38 / $0.14 | $4.82 |
| statement-generality | DeepSeek | 0 | 30 | $0.00 / — | $0.00 |
| vacuity-and-misstatement | Opus | 22 | 30 | $4.88 / $6.66 | $221.84 |
| vacuity-and-misstatement | Sol | 70 | 30 | $7.02 / $3.01 | $100.24 |
| vacuity-and-misstatement | Sonnet | 70 | 30 | $6.40 / $2.74 | $91.44 |
| vacuity-and-misstatement | Luna | 77 | 30 | $0.35 / $0.14 | $4.55 |
| vacuity-and-misstatement | DeepSeek | 0 | 30 | $0.00 / — | $0.00 |
| simp-interface | Opus | 22 | 30 | $6.52 / $8.90 | $296.52 |
| simp-interface | Sol | 70 | 30 | $7.10 / $3.04 | $101.50 |
| simp-interface | Sonnet | 70 | 30 | $6.10 / $2.61 | $87.16 |
| simp-interface | Luna | 77 | 30 | $0.36 / $0.14 | $4.63 |
| simp-interface | DeepSeek | 0 | 30 | $0.00 / — | $0.00 |
| repeated-proof-machinery | Opus | 22 | 30 | $5.56 / $7.59 | $252.95 |
| repeated-proof-machinery | Sol | 69 | 30 | $5.50 / $2.39 | $79.75 |
| repeated-proof-machinery | Sonnet | 70 | 30 | $5.22 / $2.24 | $74.57 |
| repeated-proof-machinery | Luna | 77 | 30 | $0.28 / $0.11 | $3.63 |
| repeated-proof-machinery | DeepSeek | 0 | 30 | $0.00 / — | $0.00 |
| readable-proof-simplification | Opus | 22 | 30 | $7.53 / $10.27 | $342.37 |
| readable-proof-simplification | Sol | 68 | 30 | $8.70 / $3.84 | $127.95 |
| readable-proof-simplification | Sonnet | 70 | 30 | $9.36 / $4.01 | $133.65 |
| readable-proof-simplification | Luna | 77 | 30 | $0.31 / $0.12 | $3.97 |
| readable-proof-simplification | DeepSeek | 0 | 30 | $0.00 / — | $0.00 |

## Totals by model

| Model | API-equivalent USD |
|---|---:|
| Opus | $509.85 |
| Sol | $512.12 |
| Sonnet | $273.74 |
| Luna | $24.86 |
| DeepSeek | $0.01 |
| **Total** | **$1320.58** |

## Rate sources

- [https://developers.openai.com/api/docs/pricing](https://developers.openai.com/api/docs/pricing)
- [https://platform.claude.com/docs/en/about-claude/pricing](https://platform.claude.com/docs/en/about-claude/pricing)

Frozen rates: `pricing/api-rates-2026-10-21.json`. Refresh with `python3 scripts/api_costs.py`. Mean-based projections include recorded retry expenditure and will change as more targets complete.
