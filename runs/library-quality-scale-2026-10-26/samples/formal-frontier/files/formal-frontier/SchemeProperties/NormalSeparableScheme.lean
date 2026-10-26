/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.NormalSeparable

public section

set_option warningAsError true

/-!
# Normal schemes under separable field base change

This file proves that a normal scheme remains normal after base change along a
transcendental-separable field extension. The affine calculation uses local
normality of the corresponding tensor product, and the general result descends
from an affine open cover.

Normality here does not imply that the base change is integral or connected.

## References

* R. Vakil, *The Rising Sea: Foundations of Algebraic Geometry* (October 21,
  2025 draft), Exercise 5.4.M (the separable-base-change aside).
-/

noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry

universe u

private theorem isNormal_pullback_specMap_of_isAffine
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    [Algebra.IsTranscendentalSeparable k K]
    {X : Scheme.{u}} [IsAffine X] [IsNormal X]
    (f : X ⟶ Spec (.of k)) :
    IsNormal (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) := by
  let eX := X.isoSpec
  obtain ⟨φ, hφ⟩ := Scheme.Spec.map_surjective (eX.inv ≫ f)
  algebraize [φ.unop.hom]
  have hf : f = eX.hom ≫ Spec.map φ.unop := by
    rw [← cancel_epi eX.inv]
    simpa using hφ.symm
  let e₁ : pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) ≅
      pullback (Spec.map φ.unop) (Spec.map (CommRingCat.ofHom (algebraMap k K))) :=
    asIso (pullback.map f (Spec.map (CommRingCat.ofHom (algebraMap k K)))
      (Spec.map φ.unop) (Spec.map (CommRingCat.ofHom (algebraMap k K)))
      eX.hom (𝟙 _) (𝟙 _) (by simp [hf]) (by simp))
  let _ : IsLocallyNormalRing (Γ(X, ⊤)) :=
    (isNormal_iff_isLocallyNormalRing X).mp inferInstance
  let _ : IsLocallyNormalRing (TensorProduct k (Γ(X, ⊤)) K) :=
    IsLocallyNormalRing.tensorProduct_of_isTranscendentalSeparable
  exact ObjectProperty.prop_of_iso (fun Y : Scheme => IsNormal Y)
    (e₁ ≪≫ pullbackSpecIso k (Γ(X, ⊤)) K).symm (by infer_instance)

/-- A normal scheme over a field remains normal after base change along a
transcendental-separable field extension, as in the aside to Vakil,
*The Rising Sea*, Exercise 5.4.M. -/
theorem IsNormal.pullback_specMap_of_isTranscendentalSeparable
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    [Algebra.IsTranscendentalSeparable k K]
    {X : Scheme.{u}} [IsNormal X] (f : X ⟶ Spec (.of k)) :
    IsNormal (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let 𝒰 := X.affineCover.pullback₁ (pullback.fst f g)
  let hnormal (i : 𝒰.I₀) : IsNormal (𝒰.X i) := by
    let _ : IsAffine (X.affineCover.X i) := Scheme.isAffine_affineCover X i
    let _ : IsOpenImmersion (X.affineCover.f i) := X.affineCover.map_prop i
    let _ : IsNormal (X.affineCover.X i) :=
      isNormal_of_isOpenImmersion (X.affineCover.f i)
    let e : 𝒰.X i ≅ pullback (X.affineCover.f i ≫ f) g :=
      pullbackSymmetry (pullback.fst f g) (X.affineCover.f i) ≪≫
        pullbackRightPullbackFstIso f g (X.affineCover.f i)
    have h : IsNormal (pullback (X.affineCover.f i ≫ f) g) :=
      isNormal_pullback_specMap_of_isAffine (X.affineCover.f i ≫ f)
    exact ObjectProperty.prop_of_iso (fun Y : Scheme => IsNormal Y) e.symm h
  let _ (i : 𝒰.I₀) : IsNormal (𝒰.X i) := hnormal i
  exact IsNormal.of_openCover _ 𝒰

end AlgebraicGeometry
