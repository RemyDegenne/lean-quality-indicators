# CFSG: theorem audits

Sonnet 5.5, high effort. The same 30 theorems from a fixed 2,000-target selection are used for both audits. Scope: CFSG/ excluding certificate directories. Flags are judge claims; Lean is not executed.

| Audit | Reviewed | Flagged | Rate (95% CI) | API equivalent spent |
|---|---:|---:|---:|---:|
| unnecessary-hypotheses | 15/30 | 2 | 13.3% [3.7%, 37.9%] | $1.16 |
| duplicates-mathlib-inclusive | 15/30 | 1 | 6.7% [1.2%, 29.8%] | $0.32 |

Subscription account lean-fro; actual API charges $0. Hypotheses checks use current-master Mathlib, frozen at preparation; duplication uses CFSG’s pinned Mathlib. The original prompts, schemas and validators are unchanged.
