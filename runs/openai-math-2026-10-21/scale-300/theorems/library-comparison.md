# OpenAI Math: expanded theorem audits

Sonnet 5.5, high effort. The same 200 additional theorems from a fixed 2,000-target selection are used for both audits. Scope: lean/OAI/; the original corpus selection is unchanged. Flags are judge claims; Lean is not executed.

| Audit | Reviewed | Flagged | Rate (95% CI) | API equivalent spent |
|---|---:|---:|---:|---:|
| unnecessary-hypotheses | 93/200 | 9 | 9.7% [5.2%, 17.4%] | $4.66 |
| duplicates-mathlib-inclusive | 92/200 | 4 | 4.3% [1.7%, 10.7%] | $3.08 |

Subscription account lean-fro; actual API charges $0. Hypotheses checks use current-master Mathlib, frozen at preparation; duplication uses OpenAI Math’s pinned Mathlib. The original prompts, schemas and validators are unchanged.

These counts cover targets 101–300. Main library comparisons include the original 100 judgments per audit.
