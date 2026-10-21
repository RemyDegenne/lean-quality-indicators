# Random review of Mathlib findings

Random seed: `18378141014703184964`.

uniform over individual Mathlib findings within each rubric, sorted by result filename and finding index.

One finding was selected uniformly within each category, without replacements after inspection. DFinsupp.singleton was independently drawn in two categories. These are assessments requested by the user and are separate from the unmodified Sonnet judgments.

Method: inspected the exact pinned Mathlib source and the cited definitions and proof dependencies. No Lean compilation was performed.

## concept-reinvention

Selected [DFinsupp.singleton](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Data/DFinsupp/Interval.lean#L83-L86), finding 0 of `concept-reinvention/claude-sonnet-5-5-high/results/mathlib-file-0001.json` (5 eligible findings in category).

Partly: a small implementation cleanup, not a reinvention of a mathematical concept.

DFinsupp.singleton manually maps the support witness exactly as DFinsupp.mapRange does. The zero condition is definitional: pointwise Finset zero is {0}. Reusing mapRange is reasonable, but the present implementation has only two fields and one short proof. Keeping a named singleton construction is useful; it does not create a competing mathematical concept. Sonnet overstates the severity and the concept-reinvention classification.

## statement-generality

Selected [Bundle.Trivialization.continuousLinearMapAt / symmL / continuousLinearEquivAt / apply_eq_prod_continuousLinearEquivAt / Trivialization.zeroSection](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/VectorBundle/Basic.lean#L399-L494), finding 0 of `statement-generality/claude-sonnet-5-5-high/results/mathlib-file-0006.json` (6 eligible findings in category).

Yes: a useful generalisation appears justified.

The continuous fiber maps and equivalences are defined in a section requiring NontriviallyNormedField and normed model fibers. Their construction uses only algebraic linearity, continuity of the trivialization, constant zero maps and the FiberBundle inducing property. ContinuousLinearMap and ContinuousLinearEquiv themselves are defined over semirings and additive monoids with topologies. Earlier coordChangeL already works at this generality. Moving these declarations is a real API improvement; I have not compiled the exact proposed move, including generated simps lemmas.

## vacuity-and-misstatement

Selected [Profinite.profiniteToCompHausEffectivePresentation](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/Category/Profinite/EffectiveEpi.lean#L55-L63), finding 0 of `vacuity-and-misstatement/claude-sonnet-5-5-high/results/mathlib-file-0002.json` (3 eligible findings in category).

Yes: a clear documentation error, not a vacuous mathematical result.

The docstring says X : Profinite and an inclusion from Stonean. The actual input is X : CompHaus and the functor is profiniteToCompHaus. Stonean supplies the chosen presenting object, but is not the domain of the functor for which this declaration gives an EffectivePresentation. Correcting the docstring is justified. The mathematical declaration itself is not shown defective.

## missing-structure

Selected [DFinsupp.singleton](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Data/DFinsupp/Interval.lean#L83-L86), finding 0 of `missing-structure/claude-sonnet-5-5-high/results/mathlib-file-0001.json` (4 eligible findings in category).

No, as a missing-structure finding.

This selected finding is the same DFinsupp.singleton issue drawn under concept-reinvention. The operation is already bundled as a DFinsupp. Defining it via mapRange changes implementation reuse; it does not expose a missing LinearMap, RingHom or similar structured interface. Citing Finset.singletonZeroHom does not make mapRange itself such a new interface. A small optional refactor remains possible, but the stated rubric is not demonstrated.

## simp-interface

Selected [Bundle.Trivialization.linearMapAt_def_of_notMem (and Pretrivialization.linearMapAt_def_of_notMem / linearMapAt_eq_zero)](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/VectorBundle/Basic.lean#L245-L247), finding 0 of `simp-interface/claude-sonnet-5-5-high/results/mathlib-file-0006.json` (7 eligible findings in category).

Yes: a small, sensible simp-interface improvement.

The off-base-set linearMapAt equality is present but not tagged simp, while the on-base-set coercion and both symm directions have simp rules. Rewriting the linear map to zero is a terminating, simplifying orientation. I also confirmed that Pretrivialization.linearMapAt_def_of_notMem and linearMapAt_eq_zero are identical declarations. A canonical simp rule is reasonable. I did not run the suggested simp example or downstream regression checks.

## fragile-proofs

Selected [tendsto_rpow_atTop_of_base_lt_one](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean#L53-L76), finding 1 of `fragile-proofs/claude-sonnet-5-5-high/results/mathlib-file-0003.json` (19 eligible findings in category).

No: the finding does not establish unusual fragility.

The inl/inr.inl/inr.inr case labels faithfully describe the stable nested disjunction in lt_trichotomy. The exp/cos labels belong to nested goals, so no actual conflict is shown. Reordering the statement of lt_trichotomy would be an API-breaking change that also affects the proposed positional rcases/bullet proof. Depending on a named rpow definition lemma is ordinary proof practice. Bullets are an alternative presentation, but this finding has not established a concrete maintainability defect.

## repeated-proof-machinery

Selected [Asymptotics.IsBigO.mul_atTop_rpow_of_isBigO_rpow / Asymptotics.IsBigO.mul_atTop_rpow_natCast_of_isBigO_rpow](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean#L274-L293), finding 0 of `repeated-proof-machinery/claude-sonnet-5-5-high/results/mathlib-file-0003.json` (8 eligible findings in category).

Some repeated code, but I would not call it a compelling defect.

The real-indexed and natural-indexed proofs repeat a short eventual power estimate; the natural proof adds a cast step. A helper for an arbitrary real-valued map and filter is mathematically coherent. However, the repeated block is only about six lines and is already easy to read. The extra helper, variables and filter hypothesis have a cost, and Sonnet has not shown the substantial repeated machinery required by this rubric. I regard this as an optional abstraction, not a clear quality failure.

## readable-proof-simplification

Selected [tendsto_rpow_atBot_of_base_gt_one](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean#L93-L93), finding 0 of `readable-proof-simplification/claude-sonnet-5-5-high/results/mathlib-file-0003.json` (10 eligible findings in category).

Yes: a clear readable simplification.

The goal is 0 < Real.log b and the hypothesis is hb : 1 < b. Real.log_pos has exactly that implication. The immediately preceding sibling theorem already uses exact log_pos hb. Replacing the iff/positivity/aesop expression with exact log_pos hb makes the proof both shorter and more explicit. This is a small proof cleanup rather than a correctness defect; the exact replacement was not compiled.
