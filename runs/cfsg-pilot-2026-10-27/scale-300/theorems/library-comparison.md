# CFSG: theorem audits

Sonnet 5.5, high effort. The same 270 additional theorems from a fixed 2,000-target selection are used for both audits. Scope: CFSG/ excluding certificate directories. Flags are judge claims; Lean is not executed.

| Audit | Reviewed | Flagged | Rate (95% CI) | API equivalent spent |
|---|---:|---:|---:|---:|
| unnecessary-hypotheses | 184/270 | 42 | 22.8% [17.4%, 29.4%] | $11.84 |
| duplicates-mathlib-inclusive | 184/270 | 8 | 4.3% [2.2%, 8.3%] | $4.30 |

Subscription account lean-fro; actual API charges $0. Hypotheses checks use current-master Mathlib, frozen at preparation; duplication uses CFSG’s pinned Mathlib. The original prompts, schemas and validators are unchanged.

These counts cover the 270 additional targets. The main library comparisons combine them with the original 30.
