# API-equivalent costs

Generated 2026-10-21T05:40:20+00:00 · [Methods and notation](../../AUDIT_METHODS.md).

| Audit | Model | Accepted judgments | Full-pass targets | API expenditure / full-pass estimate | USD / 1,000 judgments |
|---|---|---:|---:|---:|---:|
| unnecessary-hypotheses | Opus | 3500 | 2000 | $254.27 / $145.30 | $72.65 |
| unnecessary-hypotheses | Sol | 3000 | 2000 | $140.71 / $93.81 | $46.90 |
| unnecessary-hypotheses | Sonnet | 3000 | 2000 | $105.40 / $70.27 | $35.13 |
| unnecessary-hypotheses | Luna | 3000 | 2000 | $6.51 / $4.34 | $2.17 |
| unnecessary-hypotheses | GLM | 8 | 2000 | $0.94 / $235.29 | $117.65 |
| duplicates-mathlib-inclusive | Opus | 4000 | 5000 | $216.29 / $270.36 | $54.07 |
| duplicates-mathlib-inclusive | Sol | 5000 | 5000 | $319.51 / $319.51 | $63.90 |
| duplicates-mathlib-inclusive | Sonnet | 5000 | 5000 | $124.97 / $124.97 | $24.99 |
| duplicates-mathlib-inclusive | Luna | 5000 | 5000 | $16.00 / $16.00 | $3.20 |
| duplicates-mathlib-inclusive | GLM | 8 | 5000 | $0.23 / $145.73 | $29.15 |
| concept-reinvention | Sonnet | 30 | 30 | $2.19 / $2.19 | $72.95 |
| concept-reinvention | Luna | 30 | 30 | $0.15 / $0.15 | $5.09 |
| statement-generality | Sonnet | 30 | 30 | $3.07 / $3.07 | $102.23 |
| statement-generality | Luna | 30 | 30 | $0.15 / $0.15 | $4.93 |
| vacuity-and-misstatement | Sonnet | 30 | 30 | $2.24 / $2.24 | $74.81 |
| vacuity-and-misstatement | Luna | 30 | 30 | $0.13 / $0.13 | $4.45 |
| simp-interface | Sonnet | 30 | 30 | $2.39 / $2.39 | $79.58 |
| simp-interface | Luna | 30 | 30 | $0.15 / $0.15 | $5.00 |
| repeated-proof-machinery | Sonnet | 30 | 30 | $2.06 / $2.06 | $68.82 |
| repeated-proof-machinery | Luna | 30 | 30 | $0.11 / $0.11 | $3.59 |
| readable-proof-simplification | Sonnet | 30 | 30 | $3.52 / $3.52 | $117.17 |
| readable-proof-simplification | Luna | 30 | 30 | $0.12 / $0.12 | $4.00 |

## Totals by model

| Model | API-equivalent USD |
|---|---:|
| Opus | $470.56 |
| Sol | $460.22 |
| Sonnet | $245.84 |
| Luna | $23.32 |
| GLM | $1.17 |
| **Total** | **$1201.10** |

## GLM projection

Pilot means are early estimates; theorem and whole-file audits are projected separately.

| Audit | Accepted GLM judgments | Observed API equivalent | Planned judgments | Projected accepted-judgment cost |
|---|---:|---:|---:|---:|
| unnecessary-hypotheses | 8 | $0.941 | 50 | $5.88 |
| duplicates-mathlib-inclusive | 8 | $0.233 | 50 | $1.46 |
| concept-reinvention | 0 | $0.000 | 30 | Awaiting first accepted judgment |
| statement-generality | 0 | $0.000 | 30 | Awaiting first accepted judgment |
| vacuity-and-misstatement | 0 | $0.000 | 30 | Awaiting first accepted judgment |
| simp-interface | 0 | $0.000 | 30 | Awaiting first accepted judgment |
| repeated-proof-machinery | 0 | $0.000 | 30 | Awaiting first accepted judgment |
| readable-proof-simplification | 0 | $0.000 | 30 | Awaiting first accepted judgment |

Included in GLM hypothesis expenditure: initial parser-rejected setup calls, $0.0068 API equivalent.

## Rate sources

- [https://developers.openai.com/api/docs/pricing](https://developers.openai.com/api/docs/pricing)
- [https://platform.claude.com/docs/en/about-claude/pricing](https://platform.claude.com/docs/en/about-claude/pricing)
- [https://openrouter.ai/z-ai/glm-5.3](https://openrouter.ai/z-ai/glm-5.3)
- [https://openrouter.ai/api/v1/models](https://openrouter.ai/api/v1/models)

Frozen rates: `pricing/api-rates-2026-10-21.json`. Refresh with `python3 scripts/api_costs.py`. Mean-based projections include recorded retry expenditure and will change as more targets complete.
