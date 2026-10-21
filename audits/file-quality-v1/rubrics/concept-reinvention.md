# Its own version of a concept already in Mathlib

Does this file introduce an avoidable competing version of a concept already in Mathlib
(including Lean core or Batteries)? Apply the same question within Mathlib itself.

Useful named specialisations, wrappers, chosen orientations and deliberately different
representations are not defects merely because they can be expressed using existing
operations. In particular, implementation via a generic map or composition does not make
a named API redundant.

For a finding, read both definitions, establish that they represent the same specific
concept under matching assumptions, and show a concrete cost: duplicated substantive API,
incompatibility or repeated conversions. Check documentation and actual uses for a reason
to keep both. Propose integration while preserving useful names where appropriate.

Exclude standalone theorem duplication and proof shortening. A match must be a different,
independent declaration. If the practical case for consolidation is unclear, abstain.
