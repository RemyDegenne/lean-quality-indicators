# CFSG: theorem audits

Sonnet 5.5, high effort. The same 30 theorems from a fixed 2,000-target selection are used for both audits. Scope: CFSG/ excluding certificate directories. Flags are judge claims; Lean is not executed.

| Audit | Reviewed | Flagged | Rate (95% CI) | API equivalent spent |
|---|---:|---:|---:|---:|
| unnecessary-hypotheses | 7/30 | 1 | 14.3% [2.6%, 51.3%] | $0.52 |
| duplicates-mathlib-inclusive | 6/30 | 0 | 0.0% [0.0%, 39.0%] | $0.11 |

Subscription account lean-fro; actual API charges $0. Hypotheses checks use current-master Mathlib, frozen at preparation; duplication uses CFSG’s pinned Mathlib. The original prompts, schemas and validators are unchanged.
