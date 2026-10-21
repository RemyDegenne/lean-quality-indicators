# Random review of Mathlib findings

Random seed: `18378141014703184964`.

uniform over individual Mathlib findings within each rubric, sorted by result filename and finding index.

Findings were selected uniformly within their categories, without replacements after inspection. These are assessments requested by the user and are separate from the unmodified Sonnet judgments.

Method: inspected the exact pinned Mathlib source and the cited definitions and proof dependencies. No Lean compilation was performed.

## statement-generality

Selected [Bundle.Trivialization.continuousLinearMapAt / symmL / continuousLinearEquivAt / apply_eq_prod_continuousLinearEquivAt / Trivialization.zeroSection](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/VectorBundle/Basic.lean#L399-L494), finding 0 of `statement-generality/claude-sonnet-5-5-high/results/mathlib-file-0006.json` (6 eligible findings in category).

Yes: a useful generalisation appears justified.

The continuous fiber maps and equivalences are defined in a section requiring NontriviallyNormedField and normed model fibers. Their construction uses only algebraic linearity, continuity of the trivialization, constant zero maps and the FiberBundle inducing property. ContinuousLinearMap and ContinuousLinearEquiv themselves are defined over semirings and additive monoids with topologies. Earlier coordChangeL already works at this generality. Moving these declarations is a real API improvement; I have not compiled the exact proposed move, including generated simps lemmas.

## vacuity-and-misstatement

Selected [Profinite.profiniteToCompHausEffectivePresentation](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/Category/Profinite/EffectiveEpi.lean#L55-L63), finding 0 of `vacuity-and-misstatement/claude-sonnet-5-5-high/results/mathlib-file-0002.json` (3 eligible findings in category).

Yes: a clear documentation error, not a vacuous mathematical result.

The docstring says X : Profinite and an inclusion from Stonean. The actual input is X : CompHaus and the functor is profiniteToCompHaus. Stonean supplies the chosen presenting object, but is not the domain of the functor for which this declaration gives an EffectivePresentation. Correcting the docstring is justified. The mathematical declaration itself is not shown defective.

## simp-interface

Selected [Bundle.Trivialization.linearMapAt_def_of_notMem (and Pretrivialization.linearMapAt_def_of_notMem / linearMapAt_eq_zero)](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/VectorBundle/Basic.lean#L245-L247), finding 0 of `simp-interface/claude-sonnet-5-5-high/results/mathlib-file-0006.json` (7 eligible findings in category).

Yes: a small, sensible simp-interface improvement.

The off-base-set linearMapAt equality is present but not tagged simp, while the on-base-set coercion and both symm directions have simp rules. Rewriting the linear map to zero is a terminating, simplifying orientation. I also confirmed that Pretrivialization.linearMapAt_def_of_notMem and linearMapAt_eq_zero are identical declarations. A canonical simp rule is reasonable. I did not run the suggested simp example or downstream regression checks.

## readable-proof-simplification

Selected [tendsto_rpow_atBot_of_base_gt_one](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean#L93-L93), finding 0 of `readable-proof-simplification/claude-sonnet-5-5-high/results/mathlib-file-0003.json` (10 eligible findings in category).

Yes: a clear readable simplification.

The goal is 0 < Real.log b and the hypothesis is hb : 1 < b. Real.log_pos has exactly that implication. The immediately preceding sibling theorem already uses exact log_pos hb. Replacing the iff/positivity/aesop expression with exact log_pos hb makes the proof both shorter and more explicit. This is a small proof cleanup rather than a correctness defect; the exact replacement was not compiled.
