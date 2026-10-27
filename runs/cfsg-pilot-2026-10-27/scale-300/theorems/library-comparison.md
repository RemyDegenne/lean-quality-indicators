# CFSG: theorem audits

Sonnet 5.5, high effort. The same 270 additional theorems from a fixed 2,000-target selection are used for both audits. Scope: CFSG/ excluding certificate directories. Flags are judge claims; Lean is not executed.

| Audit | Reviewed | Flagged | Rate (95% CI) | API equivalent spent |
|---|---:|---:|---:|---:|
| unnecessary-hypotheses | 14/270 | 2 | 14.3% [4.0%, 39.9%] | $1.04 |
| duplicates-mathlib-inclusive | 14/270 | 0 | 0.0% [0.0%, 21.5%] | $0.28 |

Subscription account lean-fro; actual API charges $0. Hypotheses checks use current-master Mathlib, frozen at preparation; duplication uses CFSG’s pinned Mathlib. The original prompts, schemas and validators are unchanged.

These counts cover the 270 additional targets. The main library comparisons combine them with the original 30.
