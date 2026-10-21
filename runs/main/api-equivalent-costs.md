# API-equivalent costs

Generated 2026-10-21T05:10:00+00:00. All amounts USD.

Standard short-context API rates, including recorded cache hits/writes and reasoning output. These are API-equivalent estimates, not subscription charges. GLM is repriced at the frozen OpenRouter model-list rates, which can differ from provider-specific routing prices and the pi SDK's bundled price list. Opus baseline token counts were not retained, so its saved API-equivalent dollar amounts are used.

Counts below cover accepted judgments of the eight current audits and the original Opus duplicate baseline. Expenditure also includes separately retained retry/interrupted-call usage. Deleted experiments, this coordinating conversation, and failed calls whose usage was not saved cannot be reconstructed. They therefore do not reconstruct the entire historical bill.

Each $X / $Y cell shows recorded expenditure / estimated cost of a single pass at the largest observed pass for that audit. Y uses the model's expenditure per accepted judgment, including retained retries. The reference target count is shown explicitly. Opus duplication is the original four-library baseline, extrapolated to the five-library reference scale.

| Audit | Model | Accepted judgments | Full-pass targets | API expenditure / full-pass estimate | USD / 1,000 judgments |
|---|---|---:|---:|---:|---:|
| unnecessary-hypotheses | Opus | 3500 | 2000 | $254.27 / $145.30 | $72.65 |
| unnecessary-hypotheses | Luna | 3000 | 2000 | $6.51 / $4.34 | $2.17 |
| unnecessary-hypotheses | Sol | 3000 | 2000 | $140.71 / $93.81 | $46.90 |
| unnecessary-hypotheses | Sonnet | 3000 | 2000 | $105.40 / $70.27 | $35.13 |
| unnecessary-hypotheses | GLM | 4 | 2000 | $0.49 / $245.16 | $122.58 |
| duplicates-mathlib-inclusive | Sol | 5000 | 5000 | $319.51 / $319.51 | $63.90 |
| duplicates-mathlib-inclusive | Sonnet | 5000 | 5000 | $124.97 / $124.97 | $24.99 |
| duplicates-mathlib-inclusive | Luna | 5000 | 5000 | $16.00 / $16.00 | $3.20 |
| duplicates-mathlib-inclusive | GLM | 4 | 5000 | $0.10 / $122.62 | $24.52 |
| duplicates-mathlib-inclusive | Opus | 4000 | 5000 | $216.29 / $270.36 | $54.07 |
| concept-reinvention | Sonnet | 30 | 30 | $2.19 / $2.19 | $72.95 |
| concept-reinvention | Luna | 15 | 30 | $0.08 / $0.16 | $5.35 |
| statement-generality | Sonnet | 30 | 30 | $3.07 / $3.07 | $102.23 |
| statement-generality | Luna | 18 | 30 | $0.09 / $0.15 | $5.01 |
| vacuity-and-misstatement | Sonnet | 30 | 30 | $2.24 / $2.24 | $74.81 |
| vacuity-and-misstatement | Luna | 18 | 30 | $0.08 / $0.14 | $4.66 |
| simp-interface | Sonnet | 30 | 30 | $2.39 / $2.39 | $79.58 |
| simp-interface | Luna | 18 | 30 | $0.09 / $0.16 | $5.21 |
| repeated-proof-machinery | Sonnet | 30 | 30 | $2.06 / $2.06 | $68.82 |
| repeated-proof-machinery | Luna | 15 | 30 | $0.06 / $0.11 | $3.81 |
| readable-proof-simplification | Sonnet | 30 | 30 | $3.52 / $3.52 | $117.17 |
| readable-proof-simplification | Luna | 18 | 30 | $0.07 / $0.12 | $4.10 |

## Totals by model

| Model | API-equivalent USD |
|---|---:|
| Opus | $470.56 |
| Luna | $22.98 |
| Sol | $460.22 |
| Sonnet | $245.84 |
| GLM | $0.59 |
| **Total** | **$1200.18** |

## GLM projection

Pilot means are early estimates; theorem and whole-file audits are projected separately.

| Audit | Accepted GLM judgments | Observed API equivalent | Planned judgments | Projected accepted-judgment cost |
|---|---:|---:|---:|---:|
| unnecessary-hypotheses | 4 | $0.490 | 50 | $6.13 |
| duplicates-mathlib-inclusive | 4 | $0.098 | 50 | $1.23 |
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
