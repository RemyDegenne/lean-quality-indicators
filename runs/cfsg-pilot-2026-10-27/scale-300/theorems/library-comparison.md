# CFSG: theorem audits

Sonnet 5.5, high effort. The same 270 additional theorems from a fixed 2,000-target selection are used for both audits. Scope: CFSG/ excluding certificate directories. Flags are judge claims; Lean is not executed.

| Audit | Reviewed | Flagged | Rate (95% CI) | API equivalent spent |
|---|---:|---:|---:|---:|
| unnecessary-hypotheses | 232/270 | 53 | 22.8% [17.9%, 28.7%] | $14.71 |
| duplicates-mathlib-inclusive | 232/270 | 12 | 5.2% [3.0%, 8.8%] | $5.58 |

Subscription account lean-fro; actual API charges $0. Hypotheses checks use current-master Mathlib, frozen at preparation; duplication uses CFSG’s pinned Mathlib. The original prompts, schemas and validators are unchanged.

These counts cover the 270 additional targets. The main library comparisons combine them with the original 30.
