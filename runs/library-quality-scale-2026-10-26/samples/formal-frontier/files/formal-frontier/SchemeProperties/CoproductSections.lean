/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.OpenImmersion

public section

/-!
# Sections on coproducts of schemes

This file identifies sections on an open of an arbitrary same-universe indexed
coproduct of schemes with the dependent product of the sections on its
component preimages. The forward map is pullback to each coproduct
summand, and restriction is componentwise.

## References

- Mathlib's `AlgebraicGeometry.Limits` (`sigmaOpenCover`) and
  `AlgebraicGeometry.OpenImmersion` (`IsOpenImmersion.ΓIso`), together with
  sheaf local equality and gluing, for sections on indexed open covers.
-/

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open TopCat.Presheaf

universe u

namespace AlgebraicGeometry.Scheme

variable {ι : Type u}

noncomputable section

private def sigmaPresheafObjHom (X : ι → Scheme.{u})
    (U : (∐ X : Scheme.{u}).Opens) :
    Γ(∐ X, U) ⟶ ↧((i : ι) → Γ(X i, Sigma.ι X i ⁻¹ᵁ U)) :=
  CommRingCat.ofHom <| RingHom.pi fun i => ((Sigma.ι X i).app U).hom

private lemma sigmaSectionOpens_iSup (X : ι → Scheme.{u})
    (U : (∐ X : Scheme.{u}).Opens) :
    ⨆ i, (Sigma.ι X i).opensRange ⊓ U = U := by
  rw [← iSup_inf_eq, show (⨆ i, (Sigma.ι X i).opensRange) = ⊤ by
    calc
      _ = ⨆ i, ((sigmaOpenCover X).f i).opensRange := by congr 1
      _ = ⊤ := (sigmaOpenCover X).iSup_opensRange, top_inf_eq]

private theorem sigmaPresheafObjHom_bijective (X : ι → Scheme.{u})
    (U : (∐ X : Scheme.{u}).Opens) :
    Function.Bijective (sigmaPresheafObjHom X U) := by
  constructor
  · intro s t h
    apply (∐ X : Scheme.{u}).sheaf.eq_of_locally_eq'
      (fun i => (Sigma.ι X i).opensRange ⊓ U) U
      (fun _ => homOfLE inf_le_right) (sigmaSectionOpens_iSup X U).ge
    intro i
    have hi := congr_fun h i
    change (Sigma.ι X i).app U s = (Sigma.ι X i).app U t at hi
    calc
      ((∐ X : Scheme.{u}).presheaf.map (homOfLE inf_le_right).op) s =
          (IsOpenImmersion.ΓIso (Sigma.ι X i) U).hom ((Sigma.ι X i).app U s) :=
        (IsOpenImmersion.app_ΓIso_hom_apply (Sigma.ι X i) U s).symm
      _ = (IsOpenImmersion.ΓIso (Sigma.ι X i) U).hom ((Sigma.ι X i).app U t) := by
        exact congrArg (fun a => (IsOpenImmersion.ΓIso (Sigma.ι X i) U).hom a) hi
      _ = ((∐ X : Scheme.{u}).presheaf.map (homOfLE inf_le_right).op) t :=
        IsOpenImmersion.app_ΓIso_hom_apply (Sigma.ι X i) U t
  · intro s
    let W : ι → (∐ X : Scheme.{u}).Opens :=
      fun i => (Sigma.ι X i).opensRange ⊓ U
    let t : (i : ι) → Γ(∐ X, W i) :=
      fun i => (IsOpenImmersion.ΓIso (Sigma.ι X i) U).hom (s i)
    have ht : IsCompatible (∐ X : Scheme.{u}).presheaf W t := by
      intro i j
      by_cases hij : i = j
      · subst j
        rfl
      · have hdisj : Disjoint (W i) (W j) :=
          (disjoint_opensRange_sigmaι X i j hij).mono inf_le_left inf_le_left
        let : Subsingleton Γ(∐ X, W i ⊓ W j) :=
          CommRingCat.subsingleton_of_isTerminal <|
            (∐ X : Scheme.{u}).sheaf.isTerminalOfEqEmpty (disjoint_iff.mp hdisj)
        exact Subsingleton.elim _ _
    obtain ⟨z, hz, -⟩ := (∐ X : Scheme.{u}).sheaf.existsUnique_gluing'
      W U (fun _ => homOfLE inf_le_right) (sigmaSectionOpens_iSup X U).ge t ht
    refine ⟨z, funext fun i => ?_⟩
    have hi :
        (IsOpenImmersion.ΓIso (Sigma.ι X i) U).hom ((Sigma.ι X i).app U z) =
          (IsOpenImmersion.ΓIso (Sigma.ι X i) U).hom (s i) := by
      calc
        _ = ((∐ X : Scheme.{u}).presheaf.map (homOfLE inf_le_right).op) z :=
          IsOpenImmersion.app_ΓIso_hom_apply (Sigma.ι X i) U z
        _ = _ := hz i
    change (Sigma.ι X i).app U z = s i
    simpa only [Iso.hom_inv_id_apply] using
      congrArg (fun a => (IsOpenImmersion.ΓIso (Sigma.ι X i) U).inv a) hi

/-- Sections on an indexed coproduct of schemes are the dependent product of
the sections over the component preimages. -/
@[expose]
def sigmaPresheafObjIso (X : ι → Scheme.{u})
    (U : (∐ X : Scheme.{u}).Opens) :
    Γ(∐ X, U) ≅ ↧((i : ι) → Γ(X i, Sigma.ι X i ⁻¹ᵁ U)) :=
  let sigmaHom : Γ(∐ X, U) ⟶ ↧((i : ι) → Γ(X i, Sigma.ι X i ⁻¹ᵁ U)) :=
    CommRingCat.ofHom <| RingHom.pi fun i => ((Sigma.ι X i).app U).hom
  let sigmaHom_bijective : Function.Bijective sigmaHom := by
    constructor
    · intro s t h
      apply (∐ X : Scheme.{u}).sheaf.eq_of_locally_eq'
        (fun i => (Sigma.ι X i).opensRange ⊓ U) U
        (fun _ => homOfLE inf_le_right) (sigmaSectionOpens_iSup X U).ge
      intro i
      have hi := congr_fun h i
      change (Sigma.ι X i).app U s = (Sigma.ι X i).app U t at hi
      calc
        ((∐ X : Scheme.{u}).presheaf.map (homOfLE inf_le_right).op) s =
            (IsOpenImmersion.ΓIso (Sigma.ι X i) U).hom ((Sigma.ι X i).app U s) :=
          (IsOpenImmersion.app_ΓIso_hom_apply (Sigma.ι X i) U s).symm
        _ = (IsOpenImmersion.ΓIso (Sigma.ι X i) U).hom ((Sigma.ι X i).app U t) := by
          exact congrArg (fun a => (IsOpenImmersion.ΓIso (Sigma.ι X i) U).hom a) hi
        _ = ((∐ X : Scheme.{u}).presheaf.map (homOfLE inf_le_right).op) t :=
          IsOpenImmersion.app_ΓIso_hom_apply (Sigma.ι X i) U t
    · intro s
      let W : ι → (∐ X : Scheme.{u}).Opens :=
        fun i => (Sigma.ι X i).opensRange ⊓ U
      let t : (i : ι) → Γ(∐ X, W i) :=
        fun i => (IsOpenImmersion.ΓIso (Sigma.ι X i) U).hom (s i)
      have ht : IsCompatible (∐ X : Scheme.{u}).presheaf W t := by
        intro i j
        by_cases hij : i = j
        · subst j
          rfl
        · have hdisj : Disjoint (W i) (W j) :=
            (disjoint_opensRange_sigmaι X i j hij).mono inf_le_left inf_le_left
          let : Subsingleton Γ(∐ X, W i ⊓ W j) :=
            CommRingCat.subsingleton_of_isTerminal <|
              (∐ X : Scheme.{u}).sheaf.isTerminalOfEqEmpty (disjoint_iff.mp hdisj)
          exact Subsingleton.elim _ _
      obtain ⟨z, hz, -⟩ := (∐ X : Scheme.{u}).sheaf.existsUnique_gluing'
        W U (fun _ => homOfLE inf_le_right) (sigmaSectionOpens_iSup X U).ge t ht
      refine ⟨z, funext fun i => ?_⟩
      have hi :
          (IsOpenImmersion.ΓIso (Sigma.ι X i) U).hom ((Sigma.ι X i).app U z) =
            (IsOpenImmersion.ΓIso (Sigma.ι X i) U).hom (s i) := by
        calc
          _ = ((∐ X : Scheme.{u}).presheaf.map (homOfLE inf_le_right).op) z :=
            IsOpenImmersion.app_ΓIso_hom_apply (Sigma.ι X i) U z
          _ = _ := hz i
      change (Sigma.ι X i).app U z = s i
      simpa only [Iso.hom_inv_id_apply] using
        congrArg (fun a => (IsOpenImmersion.ΓIso (Sigma.ι X i) U).inv a) hi
  (RingEquiv.ofBijective sigmaHom.hom sigmaHom_bijective).toCommRingCatIso

private theorem sigmaPresheafObjIso_eq_oldConstruction (X : ι → Scheme.{u})
    (U : (∐ X : Scheme.{u}).Opens) :
    sigmaPresheafObjIso X U =
      (RingEquiv.ofBijective (sigmaPresheafObjHom X U).hom
        (sigmaPresheafObjHom_bijective X U)).toCommRingCatIso := by
  rfl

/-- The `i`-th coordinate of `sigmaPresheafObjIso` is pullback to the `i`-th
summand. -/
@[simp]
theorem sigmaPresheafObjIso_hom_apply (X : ι → Scheme.{u})
    (U : (∐ X : Scheme.{u}).Opens) (s : Γ(∐ X, U)) (i : ι) :
    (sigmaPresheafObjIso X U).hom s i = (Sigma.ι X i).app U s :=
  rfl

/-- Restriction of a coproduct section is coordinatewise restriction on every
summand. -/
@[simp]
theorem sigmaPresheafObjIso_hom_res_apply (X : ι → Scheme.{u})
    {V U : (∐ X : Scheme.{u}).Opens} (hVU : V ≤ U) (s : Γ(∐ X, U)) (i : ι) :
    (sigmaPresheafObjIso X V).hom
        ((∐ X : Scheme.{u}).presheaf.map (homOfLE hVU).op s) i =
      (X i).presheaf.map (homOfLE ((Sigma.ι X i).preimage_mono hVU)).op
        ((sigmaPresheafObjIso X U).hom s i) := by
  change ((Sigma.ι X i).app V)
      ((∐ X : Scheme.{u}).presheaf.map (homOfLE hVU).op s) = _
  exact ConcreteCategory.congr_hom ((Sigma.ι X i).naturality (homOfLE hVU).op) s

end

end AlgebraicGeometry.Scheme
