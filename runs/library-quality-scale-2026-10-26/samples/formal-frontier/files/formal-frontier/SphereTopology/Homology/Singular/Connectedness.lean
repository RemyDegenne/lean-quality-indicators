/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SphereTopology.Homology.Singular.Reduced

/-!
# Zeroth singular augmentation and path connectedness

The total augmentation `H₀(X; R) ⟶ R` detects path connectedness when the
coefficient object `R` is nonzero. The statement concerns this particular map,
not merely the existence of an abstract isomorphism `H₀(X; R) ≅ R`.

For integer coefficients, vanishing of reduced degree-zero homology detects
path connectedness provided the space is nonempty. Reduced degree zero here is
the kernel of the augmentation in the nonnegative theory: there is no degree
minus one term repairing the empty-space case. In particular, the empty space has
zero reduced `H₀`, even though its augmentation to a nonzero coefficient object
is not invertible.

These statements use Mathlib's component-coproduct description and augmentation
of singular `H₀`, formalized by Joël Riou, and the integral augmentation-kernel
interface of `SphereTopology.Homology.Singular.Reduced`.

## References

* J. P. May, *A Concise Course in Algebraic Topology*, Chapter 13, §2 and
  Chapter 15, §2, for the path-component description of reduced degree-zero
  integral homology. The convention here is the unbased nonnegative
  augmentation kernel; no comparison with based relative reduced homology or
  normalized chains is asserted.
-/

@[expose] public section

open CategoryTheory Limits

universe w v u

namespace TopCat

/-- A nonzero constant coproduct can fold isomorphically only over a singleton index. -/
private theorem nonempty_subsingleton_of_isIso_sigma_desc_id
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    (ι : Type w) (R : C) [HasCoproduct (fun _ : ι ↦ R)]
    (hR : ¬ IsZero R) [IsIso (Sigma.desc (fun _ : ι ↦ 𝟙 R))] :
    Nonempty ι ∧ Subsingleton ι := by
  classical
  have hn : Nonempty ι := by
    by_contra hn
    apply hR
    apply (IsZero.iff_id_eq_zero R).mpr
    apply (cancel_epi (Sigma.desc (fun _ : ι ↦ 𝟙 R))).1
    apply Sigma.hom_ext
    intro i
    exact (hn ⟨i⟩).elim
  refine ⟨hn, ⟨?_⟩⟩
  intro i j
  by_contra hij
  have hι : Sigma.ι (fun _ : ι ↦ R) i = Sigma.ι (fun _ : ι ↦ R) j := by
    apply (cancel_mono (Sigma.desc (fun _ : ι ↦ 𝟙 R))).1
    simp
  have hid : 𝟙 R = (0 : R ⟶ R) := by
    simpa only [Sigma.ι_π_eq_id, Sigma.ι_π_of_ne _ (Ne.symm hij)] using
      congrArg (fun f ↦ f ≫ Sigma.π (fun _ : ι ↦ R) i) hι
  exact hR ((IsZero.iff_id_eq_zero R).mpr hid)

/-- With a nonzero coefficient object, the total zeroth singular augmentation
is invertible exactly when the space is path connected. Path connectedness
includes nonemptiness, which is a conclusion rather than an assumption here.
The nonzero hypothesis is essential: with zero coefficients, the augmentation
is invertible even for empty or disconnected spaces. -/
theorem isIso_singularHomology₀ε_iff_pathConnectedSpace
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C]
    [Preadditive C] [CategoryWithHomology C]
    (X : TopCat.{w}) (R : C) (hR : ¬ IsZero R) :
    IsIso (X.singularHomology₀ε R) ↔ PathConnectedSpace X := by
  constructor
  · intro h
    have hcomp : IsIso ((X.singularHomology₀Iso R).hom ≫
        Sigma.desc (fun _ : ZerothHomotopy X ↦ 𝟙 R)) := by
      simpa only [singularHomology₀Iso_sigma_desc_id] using h
    have : IsIso (Sigma.desc (fun _ : ZerothHomotopy X ↦ 𝟙 R)) := by
      simpa only [isIso_comp_left_iff] using hcomp
    exact pathConnectedSpace_iff_zerothHomotopy.mpr
      (nonempty_subsingleton_of_isIso_sigma_desc_id (ZerothHomotopy X) R hR)
  · intro h
    let : PathConnectedSpace X := h
    infer_instance

/-- A nonempty space has zero reduced degree-zero integer singular homology
exactly when it is path connected. Nonemptiness is essential because reduced
`H₀` is the augmentation kernel, which also vanishes on the empty space under
the nonnegative convention; no degree minus one term is added. Compare May,
*A Concise Course in Algebraic Topology*, Chapter 13, §2 and Chapter 15, §2,
for the based reduced path-component calculation. -/
theorem isZero_reducedSingularHomologyZero_iff_pathConnectedSpace
    (X : TopCat.{w}) [Nonempty X] :
    IsZero (TopCat.reducedSingularHomologyZero X) ↔ PathConnectedSpace X := by
  constructor
  · intro h
    obtain ⟨x⟩ := ‹Nonempty X›
    let : Mono (X.singularHomology₀ε singularHomologyIntegerCoefficients) :=
      (Preadditive.mono_iff_isZero_kernel _).2 h
    let : IsSplitEpi (X.singularHomology₀ε singularHomologyIntegerCoefficients) :=
      IsSplitEpi.mk'
        { section_ := singularHomologyZeroPoint X x
          id := singularHomologyZeroPoint_augmentation X x }
    let : IsIso (X.singularHomology₀ε singularHomologyIntegerCoefficients) :=
      isIso_of_mono_of_isSplitEpi _
    have hR : ¬ IsZero (singularHomologyIntegerCoefficients.{w}) := by
      rw [ModuleCat.isZero_iff_subsingleton]
      exact not_subsingleton_iff_nontrivial.mpr inferInstance
    exact (isIso_singularHomology₀ε_iff_pathConnectedSpace
      X singularHomologyIntegerCoefficients hR).mp inferInstance
  · intro h
    let : PathConnectedSpace X := h
    exact isZero_reducedSingularHomologyZero_of_pathConnected X

end TopCat
