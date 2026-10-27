# CFSG: theorem audits

Sonnet 5.5, high effort. The same 270 additional theorems from a fixed 2,000-target selection are used for both audits. Scope: CFSG/ excluding certificate directories. Flags are judge claims; Lean is not executed.

| Audit | Reviewed | Flagged | Rate (95% CI) | API equivalent spent |
|---|---:|---:|---:|---:|
| unnecessary-hypotheses | 113/270 | 27 | 23.9% [17.0%, 32.5%] | $7.25 |
| duplicates-mathlib-inclusive | 113/270 | 3 | 2.7% [0.9%, 7.5%] | $2.66 |

Subscription account lean-fro; actual API charges $0. Hypotheses checks use current-master Mathlib, frozen at preparation; duplication uses CFSG’s pinned Mathlib. The original prompts, schemas and validators are unchanged.

These counts cover the 270 additional targets. The main library comparisons combine them with the original 30.
