# API-equivalent costs

Generated 2026-10-21T06:58:57+00:00 · [Methods and notation](../../AUDIT_METHODS.md).

| Audit | Model | Accepted judgments | Full-pass targets | API expenditure / full-pass estimate | USD / 1,000 judgments |
|---|---|---:|---:|---:|---:|
| unnecessary-hypotheses | Opus | 3515 | 2000 | $255.50 / $145.38 | $72.69 |
| unnecessary-hypotheses | Sol | 3011 | 2000 | $141.24 / $93.81 | $46.91 |
| unnecessary-hypotheses | Sonnet | 3022 | 2000 | $106.33 / $70.37 | $35.18 |
| unnecessary-hypotheses | Luna | 3020 | 2000 | $6.55 / $4.34 | $2.17 |
| duplicates-mathlib-inclusive | Opus | 4015 | 5000 | $217.36 / $270.68 | $54.14 |
| duplicates-mathlib-inclusive | Sol | 5010 | 5000 | $320.12 / $319.48 | $63.90 |
| duplicates-mathlib-inclusive | Sonnet | 5022 | 5000 | $125.69 / $125.13 | $25.03 |
| duplicates-mathlib-inclusive | Luna | 5020 | 5000 | $16.07 / $16.00 | $3.20 |
| concept-reinvention | Opus | 15 | 30 | $2.19 / $4.37 | $145.67 |
| concept-reinvention | Sol | 9 | 30 | $0.80 / $2.65 | $88.49 |
| concept-reinvention | Sonnet | 52 | 30 | $3.90 / $2.25 | $75.09 |
| concept-reinvention | Luna | 50 | 30 | $0.26 / $0.15 | $5.15 |
| statement-generality | Opus | 14 | 30 | $4.72 / $10.12 | $337.46 |
| statement-generality | Sol | 9 | 30 | $1.32 / $4.38 | $146.14 |
| statement-generality | Sonnet | 52 | 30 | $5.93 / $3.42 | $113.97 |
| statement-generality | Luna | 50 | 30 | $0.24 / $0.14 | $4.77 |
| vacuity-and-misstatement | Opus | 14 | 30 | $2.75 / $5.89 | $196.22 |
| vacuity-and-misstatement | Sol | 9 | 30 | $0.86 / $2.86 | $95.42 |
| vacuity-and-misstatement | Sonnet | 52 | 30 | $4.55 / $2.63 | $87.59 |
| vacuity-and-misstatement | Luna | 50 | 30 | $0.23 / $0.14 | $4.69 |
| simp-interface | Opus | 14 | 30 | $3.74 / $8.01 | $267.14 |
| simp-interface | Sol | 9 | 30 | $0.96 / $3.21 | $107.17 |
| simp-interface | Sonnet | 52 | 30 | $4.51 / $2.60 | $86.71 |
| simp-interface | Luna | 50 | 30 | $0.24 / $0.14 | $4.75 |
| repeated-proof-machinery | Opus | 14 | 30 | $3.67 / $7.87 | $262.39 |
| repeated-proof-machinery | Sol | 9 | 30 | $0.86 / $2.87 | $95.55 |
| repeated-proof-machinery | Sonnet | 52 | 30 | $3.73 / $2.15 | $71.66 |
| repeated-proof-machinery | Luna | 50 | 30 | $0.18 / $0.11 | $3.58 |
| readable-proof-simplification | Opus | 14 | 30 | $4.36 / $9.34 | $311.34 |
| readable-proof-simplification | Sol | 9 | 30 | $1.16 / $3.85 | $128.44 |
| readable-proof-simplification | Sonnet | 51 | 30 | $6.20 / $3.65 | $121.58 |
| readable-proof-simplification | Luna | 49 | 30 | $0.20 / $0.12 | $4.00 |

## Totals by model

| Model | API-equivalent USD |
|---|---:|
| Opus | $494.29 |
| Sol | $467.31 |
| Sonnet | $260.84 |
| Luna | $23.96 |
| **Total** | **$1246.39** |

## Rate sources

- [https://developers.openai.com/api/docs/pricing](https://developers.openai.com/api/docs/pricing)
- [https://platform.claude.com/docs/en/about-claude/pricing](https://platform.claude.com/docs/en/about-claude/pricing)

Frozen rates: `pricing/api-rates-2026-10-21.json`. Refresh with `python3 scripts/api_costs.py`. Mean-based projections include recorded retry expenditure and will change as more targets complete.
