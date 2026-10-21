# unnecessary-hypotheses: pi GLM pilot

Same first sampled theorems; one blind high-effort pass per model. Cells show positive judgments / completed judgments. No missing judgment is counted as negative.

| Library | Sol | Luna | Sonnet | GLM |
|---|---:|---:|---:|---:|
| Mathlib | 0/10 | 0/10 | 0/10 | 0/1 |
| Tau Ceti | 3/10 | 3/10 | 1/10 | 0/1 |
| Lean Pool | 2/10 | 3/10 | 1/10 | 1/1 |
| FLT (Anthropic) | 2/10 | 0/10 | 1/10 | 0/1 |
| Formal Frontier | 1/10 | 1/10 | 1/10 | 0/0 |

## Pairwise agreement

Pairs use only IDs completed by both models in the fixed pilot selection. Hypothesis details compare binder names; duplicate details compare canonical declaration names.

| First | Second | Library | N | Agree | Both positive | Same detail among both | κ |
|---|---|---|---:|---:|---:|---:|---:|
| Sol | Luna | Mathlib | 10 | 100.0% | 0 | 0/0 | — |
| Sol | Luna | Tau Ceti | 10 | 60.0% | 1 | 1/1 | 0.048 |
| Sol | Luna | Lean Pool | 10 | 90.0% | 2 | 2/2 | 0.737 |
| Sol | Luna | FLT (Anthropic) | 10 | 80.0% | 0 | 0/0 | 0.000 |
| Sol | Luna | Formal Frontier | 10 | 100.0% | 1 | 1/1 | 1.000 |
| Sol | Luna | All | 50 | 86.0% | 4 | 4/4 | 0.451 |
| Sol | Sonnet | Mathlib | 10 | 100.0% | 0 | 0/0 | — |
| Sol | Sonnet | Tau Ceti | 10 | 80.0% | 1 | 1/1 | 0.412 |
| Sol | Sonnet | Lean Pool | 10 | 90.0% | 1 | 1/1 | 0.615 |
| Sol | Sonnet | FLT (Anthropic) | 10 | 90.0% | 1 | 1/1 | 0.615 |
| Sol | Sonnet | Formal Frontier | 10 | 100.0% | 1 | 1/1 | 1.000 |
| Sol | Sonnet | All | 50 | 92.0% | 4 | 4/4 | 0.627 |
| Sol | GLM | Mathlib | 1 | 100.0% | 0 | 0/0 | — |
| Sol | GLM | Tau Ceti | 1 | 100.0% | 0 | 0/0 | — |
| Sol | GLM | Lean Pool | 1 | 100.0% | 1 | 1/1 | — |
| Sol | GLM | FLT (Anthropic) | 1 | 100.0% | 0 | 0/0 | — |
| Sol | GLM | Formal Frontier | 0 | — | 0 | 0/0 | — |
| Sol | GLM | All | 4 | 100.0% | 1 | 1/1 | 1.000 |
| Luna | Sonnet | Mathlib | 10 | 100.0% | 0 | 0/0 | — |
| Luna | Sonnet | Tau Ceti | 10 | 80.0% | 1 | 1/1 | 0.412 |
| Luna | Sonnet | Lean Pool | 10 | 80.0% | 1 | 1/1 | 0.412 |
| Luna | Sonnet | FLT (Anthropic) | 10 | 90.0% | 0 | 0/0 | 0.000 |
| Luna | Sonnet | Formal Frontier | 10 | 100.0% | 1 | 1/1 | 1.000 |
| Luna | Sonnet | All | 50 | 90.0% | 3 | 3/3 | 0.494 |
| Luna | GLM | Mathlib | 1 | 100.0% | 0 | 0/0 | — |
| Luna | GLM | Tau Ceti | 1 | 100.0% | 0 | 0/0 | — |
| Luna | GLM | Lean Pool | 1 | 100.0% | 1 | 1/1 | — |
| Luna | GLM | FLT (Anthropic) | 1 | 100.0% | 0 | 0/0 | — |
| Luna | GLM | Formal Frontier | 0 | — | 0 | 0/0 | — |
| Luna | GLM | All | 4 | 100.0% | 1 | 1/1 | 1.000 |
| Sonnet | GLM | Mathlib | 1 | 100.0% | 0 | 0/0 | — |
| Sonnet | GLM | Tau Ceti | 1 | 100.0% | 0 | 0/0 | — |
| Sonnet | GLM | Lean Pool | 1 | 100.0% | 1 | 1/1 | — |
| Sonnet | GLM | FLT (Anthropic) | 1 | 100.0% | 0 | 0/0 | — |
| Sonnet | GLM | Formal Frontier | 0 | — | 0 | 0/0 | — |
| Sonnet | GLM | All | 4 | 100.0% | 1 | 1/1 | 1.000 |

Flags and replacement arguments are model judgments. This small pilot has substantial sampling uncertainty.
