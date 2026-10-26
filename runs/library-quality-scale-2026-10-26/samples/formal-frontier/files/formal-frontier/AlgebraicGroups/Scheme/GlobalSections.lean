/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace

/-!
# Global sections along epimorphisms

This file proves that an epimorphism of schemes induces an injective map on global sections.
It also packages the resulting criterion that an affine quotient of a scheme with unchanged
global sections is trivial.

## References

- Mathlib, `AffineSpace.toSpecMvPolyIntEquiv` and
  `AffineSpace.toSpecMvPolyIntEquiv_comp`
  (`Mathlib.AlgebraicGeometry.AffineSpace`): representation of global sections
  by maps to the affine line, used with categorical epimorphism cancellation.
- Mathlib, `Flat.epi_of_flat_of_surjective` and
  `HasAffineProperty.iff_of_isAffine`: the flat-surjective specialization and
  the affine-morphism criterion used below.
-/

public section

open CategoryTheory MorphismProperty

namespace AlgebraicGeometry

universe u

/-- An epimorphism of schemes induces an injective map on global sections:
represent sections by morphisms to the affine line using Mathlib's
`AffineSpace.toSpecMvPolyIntEquiv`, then cancel the epimorphism. -/
lemma Scheme.Hom.appTop_injective_of_epi {X Y : Scheme.{u}} (f : X ⟶ Y) [Epi f] :
    Function.Injective f.appTop := by
  intro a b h
  let va : ULift.{u} (Fin 1) → Γ(Y, ⊤) := fun _ ↦ a
  let vb : ULift.{u} (Fin 1) → Γ(Y, ⊤) := fun _ ↦ b
  have hcomp : f ≫ (AffineSpace.toSpecMvPolyIntEquiv _).symm va =
      f ≫ (AffineSpace.toSpecMvPolyIntEquiv _).symm vb := by
    apply (AffineSpace.toSpecMvPolyIntEquiv (ULift.{u} (Fin 1))).injective
    funext i
    simp only [AffineSpace.toSpecMvPolyIntEquiv_comp, Equiv.apply_symm_apply, va, vb]
    exact h
  have hv : va = vb :=
    (AffineSpace.toSpecMvPolyIntEquiv (ULift.{u} (Fin 1))).symm.injective
      ((cancel_epi f).mp hcomp)
  exact congrFun hv ⟨0⟩

/-- A flat surjective morphism of schemes induces an injective map on global sections. -/
lemma Scheme.Hom.appTop_injective_of_flat_of_surjective
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [Surjective f] :
    Function.Injective f.appTop := by
  let _ : Epi f := Flat.epi_of_flat_of_surjective f
  exact f.appTop_injective_of_epi

set_option backward.isDefEq.respectTransparency false in
/-- Suppose `q : X ⟶ Y` is an epimorphism and `p : Y ⟶ Z` is affine, with `Z` affine.
If `p ∘ q` induces an isomorphism on global sections, then `p` is an isomorphism;
the proof uses Mathlib's `HasAffineProperty.iff_of_isAffine` to reduce to the
global-section map. -/
lemma IsAffineHom.isIso_of_epi_of_isIso_comp_appTop
    {X Y Z : Scheme.{u}} (q : X ⟶ Y) (p : Y ⟶ Z) [Epi q] [IsAffine Z]
    [IsAffineHom p] [IsIso ((q ≫ p).appTop)] : IsIso p := by
  rw [← isomorphisms.iff,
    HasAffineProperty.iff_of_isAffine (P := isomorphisms Scheme)]
  refine ⟨isAffine_of_isAffineHom p, ?_⟩
  rw [ConcreteCategory.isIso_iff_bijective]
  have hq : Function.Injective q.appTop := q.appTop_injective_of_epi
  have hcomp : Function.Bijective (q ≫ p).appTop :=
    ConcreteCategory.bijective_of_isIso _
  constructor
  · intro a b hab
    apply hcomp.1
    simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
    exact congrArg q.appTop hab
  · intro y
    obtain ⟨z, hz⟩ := hcomp.2 (q.appTop y)
    refine ⟨z, hq ?_⟩
    simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] using hz

/-- Suppose `q : X ⟶ Y` is flat and surjective and `p : Y ⟶ Z` is affine, with `Z` affine.
If `p ∘ q` induces an isomorphism on global sections, then `p` is an isomorphism. -/
lemma IsAffineHom.isIso_of_flat_of_surjective_of_isIso_comp_appTop
    {X Y Z : Scheme.{u}} (q : X ⟶ Y) (p : Y ⟶ Z) [Flat q] [Surjective q]
    [IsAffine Z] [IsAffineHom p] [IsIso ((q ≫ p).appTop)] : IsIso p := by
  let _ : Epi q := Flat.epi_of_flat_of_surjective q
  exact IsAffineHom.isIso_of_epi_of_isIso_comp_appTop q p

end AlgebraicGeometry
