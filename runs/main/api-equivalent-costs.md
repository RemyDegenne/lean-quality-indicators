# API-equivalent costs

Generated 2026-10-21T05:54:55+00:00 · [Methods and notation](../../AUDIT_METHODS.md).

| Audit | Model | Accepted judgments | Full-pass targets | API expenditure / full-pass estimate | USD / 1,000 judgments |
|---|---|---:|---:|---:|---:|
| unnecessary-hypotheses | Opus | 3501 | 2000 | $254.38 / $145.32 | $72.66 |
| unnecessary-hypotheses | Sol | 3001 | 2000 | $140.75 / $93.81 | $46.90 |
| unnecessary-hypotheses | Sonnet | 3003 | 2000 | $105.53 / $70.28 | $35.14 |
| unnecessary-hypotheses | Luna | 3002 | 2000 | $6.51 / $4.34 | $2.17 |
| duplicates-mathlib-inclusive | Opus | 4001 | 5000 | $216.41 / $270.44 | $54.09 |
| duplicates-mathlib-inclusive | Sol | 5001 | 5000 | $319.57 / $319.51 | $63.90 |
| duplicates-mathlib-inclusive | Sonnet | 5003 | 5000 | $125.11 / $125.04 | $25.01 |
| duplicates-mathlib-inclusive | Luna | 5002 | 5000 | $16.01 / $16.00 | $3.20 |
| concept-reinvention | Opus | 1 | 30 | $0.13 / $3.78 | $125.85 |
| concept-reinvention | Sol | 1 | 30 | $0.09 / $2.57 | $85.72 |
| concept-reinvention | Sonnet | 32 | 30 | $2.29 / $2.15 | $71.63 |
| concept-reinvention | Luna | 32 | 30 | $0.16 / $0.15 | $5.04 |
| statement-generality | Opus | 1 | 30 | $0.96 / $28.66 | $955.32 |
| statement-generality | Sol | 1 | 30 | $0.14 / $4.06 | $135.48 |
| statement-generality | Sonnet | 32 | 30 | $3.34 / $3.13 | $104.37 |
| statement-generality | Luna | 32 | 30 | $0.16 / $0.15 | $4.98 |
| vacuity-and-misstatement | Opus | 1 | 30 | $0.20 / $6.07 | $202.47 |
| vacuity-and-misstatement | Sol | 1 | 30 | $0.14 / $4.16 | $138.82 |
| vacuity-and-misstatement | Sonnet | 32 | 30 | $2.42 / $2.27 | $75.58 |
| vacuity-and-misstatement | Luna | 32 | 30 | $0.14 / $0.13 | $4.47 |
| simp-interface | Opus | 1 | 30 | $0.22 / $6.59 | $219.56 |
| simp-interface | Sol | 1 | 30 | $0.09 / $2.67 | $89.13 |
| simp-interface | Sonnet | 32 | 30 | $2.56 / $2.40 | $80.15 |
| simp-interface | Luna | 31 | 30 | $0.16 / $0.15 | $5.05 |
| repeated-proof-machinery | Opus | 0 | 30 | $0.00 / — | $0.00 |
| repeated-proof-machinery | Sol | 1 | 30 | $0.10 / $3.00 | $99.97 |
| repeated-proof-machinery | Sonnet | 32 | 30 | $2.15 / $2.01 | $67.13 |
| repeated-proof-machinery | Luna | 31 | 30 | $0.11 / $0.11 | $3.65 |
| readable-proof-simplification | Opus | 0 | 30 | $0.00 / — | $0.00 |
| readable-proof-simplification | Sol | 0 | 30 | $0.00 / — | $0.00 |
| readable-proof-simplification | Sonnet | 32 | 30 | $3.74 / $3.51 | $117.02 |
| readable-proof-simplification | Luna | 31 | 30 | $0.12 / $0.12 | $4.02 |

## Totals by model

| Model | API-equivalent USD |
|---|---:|
| Opus | $472.29 |
| Sol | $460.88 |
| Sonnet | $247.15 |
| Luna | $23.37 |
| **Total** | **$1203.69** |

## Rate sources

- [https://developers.openai.com/api/docs/pricing](https://developers.openai.com/api/docs/pricing)
- [https://platform.claude.com/docs/en/about-claude/pricing](https://platform.claude.com/docs/en/about-claude/pricing)

Frozen rates: `pricing/api-rates-2026-10-21.json`. Refresh with `python3 scripts/api_costs.py`. Mean-based projections include recorded retry expenditure and will change as more targets complete.
