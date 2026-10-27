# CFSG: theorem audits

Sonnet 5.5, high effort. The same 30 theorems from a fixed 2,000-target selection are used for both audits. Scope: CFSG/ excluding certificate directories. Flags are judge claims; Lean is not executed.

| Audit | Reviewed | Flagged | Rate (95% CI) | API equivalent spent |
|---|---:|---:|---:|---:|
| unnecessary-hypotheses | 26/30 | 3 | 11.5% [4.0%, 29.0%] | $1.69 |
| duplicates-mathlib-inclusive | 26/30 | 1 | 3.8% [0.7%, 18.9%] | $0.54 |

Subscription account lean-fro; actual API charges $0. Hypotheses checks use current-master Mathlib, frozen at preparation; duplication uses CFSG’s pinned Mathlib. The original prompts, schemas and validators are unchanged.
