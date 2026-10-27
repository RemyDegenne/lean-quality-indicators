# CFSG: theorem audits

Sonnet 5.5, high effort. The same 30 theorems from a fixed 2,000-target selection are used for both audits. Scope: CFSG/ excluding certificate directories. Flags are judge claims; Lean is not executed.

| Audit | Reviewed | Flagged | Rate (95% CI) | API equivalent spent |
|---|---:|---:|---:|---:|
| unnecessary-hypotheses | 30/30 | 4 | 13.3% [5.3%, 29.7%] | $1.86 |
| duplicates-mathlib-inclusive | 30/30 | 2 | 6.7% [1.8%, 21.3%] | $0.62 |

Subscription account lean-fro; actual API charges $0. Hypotheses checks use current-master Mathlib, frozen at preparation; duplication uses CFSG’s pinned Mathlib. The original prompts, schemas and validators are unchanged.
