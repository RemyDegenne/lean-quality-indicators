# duplicates-mathlib-inclusive: pi GLM pilot

Same first sampled theorems; one blind high-effort pass per model. Cells show positive judgments / completed judgments. No missing judgment is counted as negative.

| Library | Sol | Sonnet | Luna | GLM |
| --- | ---: | ---: | ---: | ---: |
| Mathlib | 5/10 | 3/10 | 5/10 | 2/2 |
| Tau Ceti | 1/10 | 1/10 | 0/10 | 0/1 |
| Lean Pool | 2/10 | 1/10 | 2/10 | 0/1 |
| FLT (Anthropic) | 4/10 | 1/10 | 2/10 | 1/1 |
| Formal Frontier | 1/10 | 0/10 | 1/10 | 0/1 |

## Pairwise agreement

Pairs use only IDs completed by both models in the fixed pilot selection. Hypothesis details compare binder names; duplicate details compare canonical declaration names.

| First | Second | Library | N | Agree | Both positive | Same detail among both | κ |
|---|---|---|---:|---:|---:|---:|---:|
| Sol | Luna | Mathlib | 10 | 100.0% | 5 | 3/5 | 1.000 |
| Sol | Luna | Tau Ceti | 10 | 90.0% | 0 | 0/0 | 0.000 |
| Sol | Luna | Lean Pool | 10 | 100.0% | 2 | 2/2 | 1.000 |
| Sol | Luna | FLT (Anthropic) | 10 | 80.0% | 2 | 2/2 | 0.545 |
| Sol | Luna | Formal Frontier | 10 | 100.0% | 1 | 0/1 | 1.000 |
| Sol | Luna | All | 50 | 94.0% | 10 | 7/10 | 0.831 |
| Sol | Sonnet | Mathlib | 10 | 80.0% | 3 | 2/3 | 0.600 |
| Sol | Sonnet | Tau Ceti | 10 | 100.0% | 1 | 1/1 | 1.000 |
| Sol | Sonnet | Lean Pool | 10 | 90.0% | 1 | 1/1 | 0.615 |
| Sol | Sonnet | FLT (Anthropic) | 10 | 70.0% | 1 | 1/1 | 0.286 |
| Sol | Sonnet | Formal Frontier | 10 | 90.0% | 0 | 0/0 | 0.000 |
| Sol | Sonnet | All | 50 | 86.0% | 6 | 5/6 | 0.559 |
| Sol | GLM | Mathlib | 2 | 100.0% | 2 | 1/2 | — |
| Sol | GLM | Tau Ceti | 1 | 100.0% | 0 | 0/0 | — |
| Sol | GLM | Lean Pool | 1 | 100.0% | 0 | 0/0 | — |
| Sol | GLM | FLT (Anthropic) | 1 | 0.0% | 0 | 0/0 | 0.000 |
| Sol | GLM | Formal Frontier | 1 | 100.0% | 0 | 0/0 | — |
| Sol | GLM | All | 6 | 83.3% | 2 | 1/2 | 0.667 |
| Luna | Sonnet | Mathlib | 10 | 80.0% | 3 | 3/3 | 0.600 |
| Luna | Sonnet | Tau Ceti | 10 | 90.0% | 0 | 0/0 | 0.000 |
| Luna | Sonnet | Lean Pool | 10 | 90.0% | 1 | 1/1 | 0.615 |
| Luna | Sonnet | FLT (Anthropic) | 10 | 90.0% | 1 | 1/1 | 0.615 |
| Luna | Sonnet | Formal Frontier | 10 | 90.0% | 0 | 0/0 | 0.000 |
| Luna | Sonnet | All | 50 | 88.0% | 5 | 5/5 | 0.559 |
| Luna | GLM | Mathlib | 2 | 100.0% | 2 | 2/2 | — |
| Luna | GLM | Tau Ceti | 1 | 100.0% | 0 | 0/0 | — |
| Luna | GLM | Lean Pool | 1 | 100.0% | 0 | 0/0 | — |
| Luna | GLM | FLT (Anthropic) | 1 | 0.0% | 0 | 0/0 | 0.000 |
| Luna | GLM | Formal Frontier | 1 | 100.0% | 0 | 0/0 | — |
| Luna | GLM | All | 6 | 83.3% | 2 | 2/2 | 0.667 |
| Sonnet | GLM | Mathlib | 2 | 50.0% | 1 | 1/1 | 0.000 |
| Sonnet | GLM | Tau Ceti | 1 | 100.0% | 0 | 0/0 | — |
| Sonnet | GLM | Lean Pool | 1 | 100.0% | 0 | 0/0 | — |
| Sonnet | GLM | FLT (Anthropic) | 1 | 0.0% | 0 | 0/0 | 0.000 |
| Sonnet | GLM | Formal Frontier | 1 | 100.0% | 0 | 0/0 | — |
| Sonnet | GLM | All | 6 | 66.7% | 1 | 1/1 | 0.333 |

Flags and replacement arguments are model judgments. This small pilot has substantial sampling uncertainty.
