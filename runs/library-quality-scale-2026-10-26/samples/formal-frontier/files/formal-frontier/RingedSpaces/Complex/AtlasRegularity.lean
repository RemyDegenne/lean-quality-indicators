/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ComplexAnalysis.Analysis.Complex.FiniteDimensional
public import Mathlib.Geometry.Manifold.IsManifold.Basic

/-!
# Complex regularity of a fixed atlas

For a boundaryless complex model with finite-dimensional normed coordinate space, complex
differentiability of every ordered atlas transition on its exact model-coordinate domain gives
analytic manifold regularity for the **given** charted space. Smooth regularity at `∞` follows
from regularity at the distinct analytic index `ω`. An existing order-one manifold structure
also supplies the differentiability hypothesis.

The conclusion concerns the atlas on the given charted space; it does not change charts or
identify any structure sheaf. The boundaryless assumption makes the transition domains open
in the entire model vector space. No statement about models with arbitrary corners is made.

## References

* Formal Frontier, `ComplexAnalysis/Analysis/Complex/FiniteDimensional.lean`:
  differentiability of a finite-dimensional complex map on an open set implies
  local analyticity.
* Mathlib, `Mathlib/Geometry/Manifold/ContMDiff/Atlas.lean`
  (Sébastien Gouëzel and Floris van Doorn):
  `isManifold_of_contDiffOn` on the specified chart transitions.
* Ravi Vakil, *The Rising Sea: Foundations of Algebraic Geometry* (October 21, 2025
  draft), Definition 4.3.9 (p. 142): motivation for complex chart models,
  not a proof that differentiable ordered transitions of a specified boundaryless
  finite-dimensional atlas give analytic `ω` and then smooth `∞` regularity.
  This does not reconstruct an arbitrary sheaf or treat corners or real differentiability.
-/

@[expose] public section

open scoped ContDiff Manifold

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E]
variable {H : Type v} [TopologicalSpace H]
variable (I : ModelWithCorners ℂ E H) [I.Boundaryless]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/-- Complex differentiability of all ordered transitions in model coordinates makes the
existing charted space an analytic complex manifold. The domain is exactly the preimage of
the transition source under `I.symm`, intersected with the range of `I`.
The implication from complex differentiability to analytic transitions uses
`DifferentiableOn.analyticOnNhd_of_finiteDimensional` from Formal Frontier's
`ComplexAnalysis.Analysis.Complex.FiniteDimensional`. -/
theorem isManifold_omega_of_differentiableOn_chartTransitions
    (h : ∀ e e' : OpenPartialHomeomorph M H,
      e ∈ atlas H M → e' ∈ atlas H M →
      DifferentiableOn ℂ (I ∘ (e.symm ≫ₕ e') ∘ I.symm)
        (I.symm ⁻¹' (e.symm ≫ₕ e').source ∩ Set.range I)) :
    IsManifold I ω M := by
  have : CompleteSpace E := FiniteDimensional.complete ℂ E
  apply isManifold_of_contDiffOn I ω M
  intro e e' he he'
  have hOpen : IsOpen (I.symm ⁻¹' (e.symm ≫ₕ e').source ∩ Set.range I) := by
    rw [I.range_eq_univ, Set.inter_univ]
    exact (e.symm ≫ₕ e').open_source.preimage I.continuous_symm
  exact ((h e e' he he').analyticOnNhd_of_finiteDimensional hOpen).contDiffOn_of_completeSpace

/-- The same raw complex-differentiability criterion gives complex smoothness (`∞`) on the
given charts. The stronger analytic regularity (`ω`) is obtained first. -/
theorem isManifold_infty_of_differentiableOn_chartTransitions
    (h : ∀ e e' : OpenPartialHomeomorph M H,
      e ∈ atlas H M → e' ∈ atlas H M →
      DifferentiableOn ℂ (I ∘ (e.symm ≫ₕ e') ∘ I.symm)
        (I.symm ⁻¹' (e.symm ≫ₕ e').source ∩ Set.range I)) :
    IsManifold I ∞ M := by
  have : IsManifold I ω M := isManifold_omega_of_differentiableOn_chartTransitions I h
  exact IsManifold.of_le le_top

/-- An order-one complex manifold with a finite-dimensional boundaryless model has analytic
regularity on the same atlas. This is a convenient corollary of the raw transition criterion,
not a replacement for it. -/
theorem isManifold_omega_of_isManifold_one [IsManifold I 1 M] :
    IsManifold I ω M := by
  apply isManifold_omega_of_differentiableOn_chartTransitions I
  intro e e' he he'
  have hGroupoid : e.symm ≫ₕ e' ∈ contDiffGroupoid 1 I :=
    (contDiffGroupoid 1 I).compatible he he'
  have hDiff : ContDiffOn ℂ 1 (I ∘ (e.symm ≫ₕ e') ∘ I.symm)
      (I.symm ⁻¹' (e.symm ≫ₕ e').source ∩ Set.range I) :=
    (mem_groupoid_of_pregroupoid.mp hGroupoid).1
  exact hDiff.differentiableOn_one
