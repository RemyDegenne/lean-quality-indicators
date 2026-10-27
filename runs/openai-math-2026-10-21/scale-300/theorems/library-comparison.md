# OpenAI Math: expanded theorem audits

Sonnet 5.5, high effort. The same 200 additional theorems from a fixed 2,000-target selection are used for both audits. Scope: lean/OAI/; the original corpus selection is unchanged. Flags are judge claims; Lean is not executed.

| Audit | Reviewed | Flagged | Rate (95% CI) | API equivalent spent |
|---|---:|---:|---:|---:|
| unnecessary-hypotheses | 101/200 | 13 | 12.9% [7.7%, 20.8%] | $5.28 |
| duplicates-mathlib-inclusive | 101/200 | 4 | 4.0% [1.6%, 9.7%] | $3.39 |

Subscription account lean-fro; actual API charges $0. Hypotheses checks use current-master Mathlib, frozen at preparation; duplication uses OpenAI Math’s pinned Mathlib. The original prompts, schemas and validators are unchanged.

These counts cover targets 101–300. Main library comparisons include the original 100 judgments per audit.
