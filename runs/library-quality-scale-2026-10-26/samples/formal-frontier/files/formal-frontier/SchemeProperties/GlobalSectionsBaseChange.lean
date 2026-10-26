/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.TensorProduct.Maps

public section

/-!
# Global sections after extension of the base field

For a quasicompact quasiseparated scheme `X` over a field `k`, this file
identifies the global sections of the base change to an extension field `K`
with `K ⊗[k] Γ(X, ⊤)`.  The equivalence is the canonical one: it sends the two
tensor-product generators to the maps on global sections induced by the two
pullback projections.

The proof specializes mathlib's flat base-change theorem for sections on qcqs
opens.  In particular, `X` is not assumed affine, separated, reduced,
connected, or nonempty, and the extension is not assumed finite.

The canonical equivalence below also satisfies identity and tower coherence.

## References

- Mathlib, `Mathlib.AlgebraicGeometry.Morphisms.Flat`,
  `isIso_pushoutSection_of_isQuasiSeparated_of_flat_right`: flat base change
  for sections on a quasi-compact quasiseparated source open over affine base
  opens, specialized here to global sections after a field extension.
-/

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped TensorProduct

universe u

noncomputable section

namespace AlgebraicGeometry
namespace Scheme

/-- The `k`-algebra structure on the global sections of a scheme over `k`.

This is kept as an explicit definition because the structure morphism is data,
not a typeclass parameter of the scheme. -/
@[instance_reducible, expose]
def Hom.globalSectionsAlgebra (k : Type u) [CommRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) : Algebra k Γ(X, ⊤) :=
  (p.appTop.hom.comp (ΓSpecIso (.of k)).inv.hom).toAlgebra

/-- The `K`-algebra structure on the global sections of the base change of a
scheme along `k → K`. -/
@[instance_reducible, expose]
def Hom.baseChangeGlobalSectionsAlgebra (k K : Type u) [CommRing k] [CommRing K]
    [Algebra k K] {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) :
    Algebra K Γ(pullback p (Spec.map (CommRingCat.ofHom (algebraMap k K))), ⊤) :=
  ((pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k K)))).appTop.hom.comp
    (ΓSpecIso (.of K)).inv.hom).toAlgebra

private theorem globalSectionsBaseChange_isPushout
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of k))
    [CompactSpace X] [QuasiSeparatedSpace X] :
    letI := p.globalSectionsAlgebra k
    IsPushout
      (CommRingCat.ofHom (algebraMap k Γ(X, ⊤)))
      (CommRingCat.ofHom (algebraMap k K))
      (pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap k K)))).appTop
      ((ΓSpecIso (.of K)).inv ≫
        (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k K)))).appTop) := by
  let _ := p.globalSectionsAlgebra k
  let s : Spec (.of K) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let H : IsPullback (pullback.fst p s) (pullback.snd p s) p s :=
    IsPullback.of_hasPullback p s
  let _ : Flat s := Flat.SpecMap_iff.mpr
    (RingHom.Flat.of_isField (R := k) (S := K) (Field.toIsField k) (algebraMap k K))
  let US : (Spec (.of k)).Opens := ⊤
  let UT : (Spec (.of K)).Opens := ⊤
  let UX : X.Opens := ⊤
  let UY : (pullback p s).Opens := ⊤
  have hs : IsIso (pushoutSection H (US := US) (UT := UT) (UX := UX) (UY := UY)
      (by simp [US, UT, s]) (by simp [US, UX]) (by simp [UY, UX, UT])) :=
    isIso_pushoutSection_of_isQuasiSeparated_of_flat_right H
      (by simp [US, UT, s]) (by simp [US, UX]) (by simp [UY, UX, UT])
      (isAffineOpen_top _) (isAffineOpen_top _)
      CompactSpace.isCompact_univ isQuasiSeparated_univ
  have h₀ : IsPushout p.appTop s.appTop (pullback.fst p s).appTop
      (pullback.snd p s).appTop := by
    have := hs
    let hh :=
      (isIso_pushoutSection_iff H (US := US) (UT := UT) (UX := UX) (UY := UY)
        (by simp [US, UT, s]) (by simp [US, UX]) (by simp [UY, UX, UT])).mp this
    simpa only [US, UT, UX, UY, s, H, Hom.app_eq_appLE, Hom.preimage_top,
      inf_idem] using hh
  have h : IsPushout
      (CommRingCat.ofHom (algebraMap k Γ(X, ⊤)))
      (CommRingCat.ofHom (algebraMap k K))
      (pullback.fst p s).appTop
      ((ΓSpecIso (.of K)).inv ≫ (pullback.snd p s).appTop) := by
    apply h₀.of_iso (ΓSpecIso (.of k)) (Iso.refl _) (ΓSpecIso (.of K)) (Iso.refl _)
    · rw [← cancel_epi (ΓSpecIso (.of k)).inv]
      simp only [Iso.inv_hom_id_assoc]
      change (ΓSpecIso (.of k)).inv ≫ p.appTop =
        CommRingCat.ofHom (p.appTop.hom.comp (ΓSpecIso (.of k)).inv.hom)
      rfl
    · exact ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap k K))
    · simp
    · simp
  simpa only [s] using h

/-- Global sections of a quasicompact quasiseparated scheme commute with
extension of the base field.

The source is oriented with the extension field on the left.  The algebra
structures occurring in the type are the canonical structures defined by the
structure morphism and the second pullback projection. The proof specializes
Mathlib's `isIso_pushoutSection_of_isQuasiSeparated_of_flat_right` to global
sections and identifies the resulting pushout with the tensor product. -/
@[expose]
noncomputable def globalSectionsBaseChangeEquiv
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of k))
    [CompactSpace X] [QuasiSeparatedSpace X] :
    letI := p.globalSectionsAlgebra k
    letI := p.baseChangeGlobalSectionsAlgebra k K
    K ⊗[k] Γ(X, ⊤) ≃ₐ[K]
      Γ(pullback p (Spec.map (CommRingCat.ofHom (algebraMap k K))), ⊤) := by
  let _ := p.globalSectionsAlgebra k
  let _ := p.baseChangeGlobalSectionsAlgebra k K
  let s : Spec (.of K) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let h : IsPushout
      (CommRingCat.ofHom (algebraMap k Γ(X, ⊤)))
      (CommRingCat.ofHom (algebraMap k K))
      (pullback.fst p s).appTop
      ((ΓSpecIso (.of K)).inv ≫ (pullback.snd p s).appTop) := by
    let H : IsPullback (pullback.fst p s) (pullback.snd p s) p s :=
      IsPullback.of_hasPullback p s
    let _ : Flat s := Flat.SpecMap_iff.mpr
      (RingHom.Flat.of_isField (R := k) (S := K) (Field.toIsField k) (algebraMap k K))
    let US : (Spec (.of k)).Opens := ⊤
    let UT : (Spec (.of K)).Opens := ⊤
    let UX : X.Opens := ⊤
    let UY : (pullback p s).Opens := ⊤
    have hs : IsIso (pushoutSection H (US := US) (UT := UT) (UX := UX) (UY := UY)
        (by simp [US, UT, s]) (by simp [US, UX]) (by simp [UY, UX, UT])) :=
      isIso_pushoutSection_of_isQuasiSeparated_of_flat_right H
        (by simp [US, UT, s]) (by simp [US, UX]) (by simp [UY, UX, UT])
        (isAffineOpen_top _) (isAffineOpen_top _)
        CompactSpace.isCompact_univ isQuasiSeparated_univ
    have h₀ : IsPushout p.appTop s.appTop (pullback.fst p s).appTop
        (pullback.snd p s).appTop := by
      have := hs
      let hh :=
        (isIso_pushoutSection_iff H (US := US) (UT := UT) (UX := UX) (UY := UY)
          (by simp [US, UT, s]) (by simp [US, UX]) (by simp [UY, UX, UT])).mp this
      simpa only [US, UT, UX, UY, s, H, Hom.app_eq_appLE, Hom.preimage_top,
        inf_idem] using hh
    have h' : IsPushout
        (CommRingCat.ofHom (algebraMap k Γ(X, ⊤)))
        (CommRingCat.ofHom (algebraMap k K))
        (pullback.fst p s).appTop
        ((ΓSpecIso (.of K)).inv ≫ (pullback.snd p s).appTop) := by
      apply h₀.of_iso (ΓSpecIso (.of k)) (Iso.refl _) (ΓSpecIso (.of K)) (Iso.refl _)
      · rw [← cancel_epi (ΓSpecIso (.of k)).inv]
        simp only [Iso.inv_hom_id_assoc]
        change (ΓSpecIso (.of k)).inv ≫ p.appTop =
          CommRingCat.ofHom (p.appTop.hom.comp (ΓSpecIso (.of k)).inv.hom)
        rfl
      · exact ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap k K))
      · simp
      · simp
    exact h'
  let hTensor := (CommRingCat.isPushout_tensorProduct k K Γ(X, ⊤)).flip
  let e := hTensor.isoIsPushout (CommRingCat.of Γ(X, ⊤)) (CommRingCat.of K) h
  exact
    { toRingEquiv := e.commRingCatIsoToRingEquiv
      commutes' r := by
        change (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom ≫ e.hom) r =
          ((ΓSpecIso (.of K)).inv ≫ (pullback.snd p s).appTop) r
        exact congr($(hTensor.inr_isoIsPushout_hom
          (CommRingCat.of Γ(X, ⊤)) (CommRingCat.of K) h) r) }

private theorem globalSectionsBaseChangeEquiv_eq_oldConstruction
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of k))
    [CompactSpace X] [QuasiSeparatedSpace X] :
    letI := p.globalSectionsAlgebra k
    letI := p.baseChangeGlobalSectionsAlgebra k K
    globalSectionsBaseChangeEquiv k K p =
      let h := globalSectionsBaseChange_isPushout k K p
      let hTensor := (CommRingCat.isPushout_tensorProduct k K Γ(X, ⊤)).flip
      let e := hTensor.isoIsPushout (CommRingCat.of Γ(X, ⊤)) (CommRingCat.of K) h
      { toRingEquiv := e.commRingCatIsoToRingEquiv
        commutes' r := by
          change (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom ≫ e.hom) r =
            ((ΓSpecIso (.of K)).inv ≫
              (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k K)))).appTop) r
          exact congr($(hTensor.inr_isoIsPushout_hom
            (CommRingCat.of Γ(X, ⊤)) (CommRingCat.of K) h) r) } := by
  rfl

/-- On the scalar generator, the base-change equivalence is the map induced by
the projection to `Spec K`. -/
theorem globalSectionsBaseChangeEquiv_tmul_one
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of k))
    [CompactSpace X] [QuasiSeparatedSpace X] (r : K) :
    letI := p.globalSectionsAlgebra k
    letI := p.baseChangeGlobalSectionsAlgebra k K
    globalSectionsBaseChangeEquiv k K p (r ⊗ₜ[k] (1 : Γ(X, ⊤))) =
      (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k K)))).appTop
        ((ΓSpecIso (.of K)).inv r) := by
  let _ := p.globalSectionsAlgebra k
  let _ := p.baseChangeGlobalSectionsAlgebra k K
  let s : Spec (.of K) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let h := globalSectionsBaseChange_isPushout k K p
  let hTensor := (CommRingCat.isPushout_tensorProduct k K Γ(X, ⊤)).flip
  let e := hTensor.isoIsPushout (CommRingCat.of Γ(X, ⊤)) (CommRingCat.of K) h
  change e.hom (r ⊗ₜ[k] (1 : Γ(X, ⊤))) =
    (pullback.snd p s).appTop ((ΓSpecIso (.of K)).inv r)
  exact congr($(hTensor.inr_isoIsPushout_hom
    (CommRingCat.of Γ(X, ⊤)) (CommRingCat.of K) h) r)

/-- On the global-section generator, the base-change equivalence is the map
induced by the projection to `X`. -/
theorem globalSectionsBaseChangeEquiv_one_tmul
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of k))
    [CompactSpace X] [QuasiSeparatedSpace X] (x : Γ(X, ⊤)) :
    letI := p.globalSectionsAlgebra k
    letI := p.baseChangeGlobalSectionsAlgebra k K
    globalSectionsBaseChangeEquiv k K p ((1 : K) ⊗ₜ[k] x) =
      (pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap k K)))).appTop x := by
  let _ := p.globalSectionsAlgebra k
  let _ := p.baseChangeGlobalSectionsAlgebra k K
  let s : Spec (.of K) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let h := globalSectionsBaseChange_isPushout k K p
  let hTensor := (CommRingCat.isPushout_tensorProduct k K Γ(X, ⊤)).flip
  let e := hTensor.isoIsPushout (CommRingCat.of Γ(X, ⊤)) (CommRingCat.of K) h
  change e.hom ((1 : K) ⊗ₜ[k] x) = (pullback.fst p s).appTop x
  exact congr($(hTensor.inl_isoIsPushout_hom
    (CommRingCat.of Γ(X, ⊤)) (CommRingCat.of K) h) x)

/-- Formula for the canonical base-change equivalence on an arbitrary pure
tensor. -/
@[simp]
theorem globalSectionsBaseChangeEquiv_tmul
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of k))
    [CompactSpace X] [QuasiSeparatedSpace X] (r : K) (x : Γ(X, ⊤)) :
    letI := p.globalSectionsAlgebra k
    letI := p.baseChangeGlobalSectionsAlgebra k K
    globalSectionsBaseChangeEquiv k K p (r ⊗ₜ[k] x) =
      (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k K)))).appTop
          ((ΓSpecIso (.of K)).inv r) *
        (pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap k K)))).appTop x := by
  let _ := p.globalSectionsAlgebra k
  let _ := p.baseChangeGlobalSectionsAlgebra k K
  rw [show r ⊗ₜ[k] x = (r ⊗ₜ[k] (1 : Γ(X, ⊤))) * ((1 : K) ⊗ₜ[k] x) by simp,
    map_mul, globalSectionsBaseChangeEquiv_tmul_one,
    globalSectionsBaseChangeEquiv_one_tmul]

/-- Base change along the identity extension is canonically isomorphic to the
original scheme. -/
noncomputable def baseChangeIdentityIso
    (k : Type u) [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) :
    pullback p (Spec.map (CommRingCat.ofHom (algebraMap k k))) ≅ X := by
  let s := Spec.map (CommRingCat.ofHom (algebraMap k k))
  let _ : IsIso s := by
    dsimp [s]
    infer_instance
  exact asIso (pullback.fst p s)

@[reassoc]
theorem baseChangeIdentityIso_hom
    (k : Type u) [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) :
    (baseChangeIdentityIso k p).hom =
      pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap k k))) := by
  rfl

attribute [simp] baseChangeIdentityIso_hom

@[reassoc]
theorem baseChangeIdentityIso_inv_fst
    (k : Type u) [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) :
    (baseChangeIdentityIso k p).inv ≫
        pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap k k))) = 𝟙 X := by
  rw [← baseChangeIdentityIso_hom]
  exact Iso.inv_hom_id _

@[reassoc]
theorem baseChangeIdentityIso_inv_snd
    (k : Type u) [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) :
    (baseChangeIdentityIso k p).inv ≫
        pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k k))) = p := by
  let s := Spec.map (CommRingCat.ofHom (algebraMap k k))
  let _ : IsIso s := by
    dsimp [s]
    infer_instance
  rw [← cancel_mono (Spec.map (CommRingCat.ofHom (algebraMap k k)))]
  rw [Category.assoc, ← pullback.condition, ← Category.assoc,
    baseChangeIdentityIso_inv_fst, Category.id_comp]
  simp

theorem baseChangeIdentityIso_inv_appTop_fst
    (k : Type u) [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k))
    (x : Γ(X, ⊤)) :
    (baseChangeIdentityIso k p).inv.appTop
        ((pullback.fst p
          (Spec.map (CommRingCat.ofHom (algebraMap k k)))).appTop x) = x := by
  have h := congrArg Hom.appTop (baseChangeIdentityIso_inv_fst k p)
  simp only [Hom.comp_appTop] at h
  exact congr($h x)

theorem baseChangeIdentityIso_inv_appTop_snd
    (k : Type u) [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k))
    (x : Γ(Spec (.of k), ⊤)) :
    (baseChangeIdentityIso k p).inv.appTop
        ((pullback.snd p
          (Spec.map (CommRingCat.ofHom (algebraMap k k)))).appTop x) = p.appTop x := by
  have h := congrArg Hom.appTop (baseChangeIdentityIso_inv_snd k p)
  simp only [Hom.comp_appTop] at h
  exact congr($h x)

/-- Transport of global sections along identity base change. -/
noncomputable def globalSectionsBaseChangeIdentityEquiv
    (k : Type u) [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) :
    letI := p.baseChangeGlobalSectionsAlgebra k k
    letI := p.globalSectionsAlgebra k
    Γ(pullback p (Spec.map (CommRingCat.ofHom (algebraMap k k))), ⊤) ≃ₐ[k]
      Γ(X, ⊤) := by
  let _ := p.baseChangeGlobalSectionsAlgebra k k
  let _ := p.globalSectionsAlgebra k
  let e := baseChangeIdentityIso k p
  letI : IsIso e.inv := by dsimp [e]; infer_instance
  letI : IsIso (e.inv.app (⊤ : (pullback p
      (Spec.map (CommRingCat.ofHom (algebraMap k k)))).Opens)) := inferInstance
  exact
    { toRingEquiv := (asIso (e.inv.app (⊤ : (pullback p
          (Spec.map (CommRingCat.ofHom (algebraMap k k)))).Opens))).commRingCatIsoToRingEquiv
      commutes' r := by
        change (e.inv.appTop.hom.comp
            ((pullback.snd p
              (Spec.map (CommRingCat.ofHom (algebraMap k k)))).appTop.hom.comp
              (ΓSpecIso (.of k)).inv.hom)) r =
          (p.appTop.hom.comp (ΓSpecIso (.of k)).inv.hom) r
        congr 1
        rw [← RingHom.comp_assoc, ← CommRingCat.hom_comp, ← Hom.comp_appTop,
          baseChangeIdentityIso_inv_snd] }

theorem globalSectionsBaseChangeIdentityEquiv_apply
    (k : Type u) [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k))
    (x : Γ(pullback p (Spec.map (CommRingCat.ofHom (algebraMap k k))), ⊤)) :
    letI := p.baseChangeGlobalSectionsAlgebra k k
    letI := p.globalSectionsAlgebra k
    globalSectionsBaseChangeIdentityEquiv k p x =
      (baseChangeIdentityIso k p).inv.appTop x := by
  rfl

/-- The canonical global-sections equivalence for the identity field extension
is the tensor-product left unitor after transporting along
`baseChangeIdentityIso`. -/
theorem globalSectionsBaseChangeEquiv_identity
    (k : Type u) [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k))
    [CompactSpace X] [QuasiSeparatedSpace X] :
    letI := p.globalSectionsAlgebra k
    letI := p.baseChangeGlobalSectionsAlgebra k k
    (globalSectionsBaseChangeEquiv k k p).trans
        (globalSectionsBaseChangeIdentityEquiv k p) =
      Algebra.TensorProduct.lid k Γ(X, ⊤) := by
  let _ := p.globalSectionsAlgebra k
  let _ := p.baseChangeGlobalSectionsAlgebra k k
  apply AlgEquiv.coe_toAlgHom_injective
  apply Algebra.TensorProduct.ext'
  intro r x
  change globalSectionsBaseChangeIdentityEquiv k p
      (globalSectionsBaseChangeEquiv k k p (r ⊗ₜ[k] x)) = r • x
  rw [globalSectionsBaseChangeEquiv_tmul,
    globalSectionsBaseChangeIdentityEquiv_apply,
    map_mul, baseChangeIdentityIso_inv_appTop_fst]
  rw [baseChangeIdentityIso_inv_appTop_snd]
  rfl

private theorem baseChangeTower_isPullback
    (k K L : Type u) [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra K L] [Algebra k L] [IsScalarTower k K L]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) : IsPullback
      (pullback.fst
          (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k K))))
          (Spec.map (CommRingCat.ofHom (algebraMap K L))) ≫
        pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap k K))))
      (pullback.snd
        (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k K))))
        (Spec.map (CommRingCat.ofHom (algebraMap K L))))
      p (Spec.map (CommRingCat.ofHom (algebraMap k L))) := by
  let sK := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let sL := Spec.map (CommRingCat.ofHom (algebraMap K L))
  have h := (IsPullback.of_hasPullback (pullback.snd p sK) sL).paste_horiz
    (IsPullback.of_hasPullback p sK)
  have hs : sL ≫ sK = Spec.map (CommRingCat.ofHom (algebraMap k L)) := by
    rw [← Spec.map_comp]
    congr 1
    ext x
    simp [IsScalarTower.algebraMap_apply k K L]
  rw [hs] at h
  exact h

/-- The canonical identification between successive base change through
`k → K → L` and direct base change from `k` to `L`. -/
@[expose]
noncomputable def baseChangeTowerIso
    (k K L : Type u) [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra K L] [Algebra k L] [IsScalarTower k K L]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) :
    pullback
        (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k K))))
        (Spec.map (CommRingCat.ofHom (algebraMap K L))) ≅
      pullback p (Spec.map (CommRingCat.ofHom (algebraMap k L))) :=
  (show IsPullback
      (pullback.fst
          (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k K))))
          (Spec.map (CommRingCat.ofHom (algebraMap K L))) ≫
        pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap k K))))
      (pullback.snd
        (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k K))))
        (Spec.map (CommRingCat.ofHom (algebraMap K L))))
      p (Spec.map (CommRingCat.ofHom (algebraMap k L))) from by
    let sK := Spec.map (CommRingCat.ofHom (algebraMap k K))
    let sL := Spec.map (CommRingCat.ofHom (algebraMap K L))
    have h := (IsPullback.of_hasPullback (pullback.snd p sK) sL).paste_horiz
      (IsPullback.of_hasPullback p sK)
    have hs : sL ≫ sK = Spec.map (CommRingCat.ofHom (algebraMap k L)) := by
      rw [← Spec.map_comp]
      congr 1
      ext x
      simp [IsScalarTower.algebraMap_apply k K L]
    rw [hs] at h
    exact h).isoIsPullback X (Spec (.of L))
    (IsPullback.of_hasPullback p (Spec.map (CommRingCat.ofHom (algebraMap k L))))

private theorem baseChangeTowerIso_eq_oldConstruction
    (k K L : Type u) [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra K L] [Algebra k L] [IsScalarTower k K L]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) :
    baseChangeTowerIso k K L p =
      (baseChangeTower_isPullback k K L p).isoIsPullback X (Spec (.of L))
        (IsPullback.of_hasPullback p (Spec.map (CommRingCat.ofHom (algebraMap k L)))) := by
  rfl

@[reassoc (attr := simp)]
theorem baseChangeTowerIso_hom_fst
    (k K L : Type u) [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra K L] [Algebra k L] [IsScalarTower k K L]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) :
    (baseChangeTowerIso k K L p).hom ≫
        pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap k L))) =
      pullback.fst
          (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k K))))
          (Spec.map (CommRingCat.ofHom (algebraMap K L))) ≫
      pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
  exact (baseChangeTower_isPullback k K L p).isoIsPullback_hom_fst _ _
    (IsPullback.of_hasPullback p (Spec.map (CommRingCat.ofHom (algebraMap k L))))

@[reassoc (attr := simp)]
theorem baseChangeTowerIso_hom_snd
    (k K L : Type u) [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra K L] [Algebra k L] [IsScalarTower k K L]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) :
    (baseChangeTowerIso k K L p).hom ≫
        pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k L))) =
      pullback.snd
        (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k K))))
        (Spec.map (CommRingCat.ofHom (algebraMap K L))) := by
  exact (baseChangeTower_isPullback k K L p).isoIsPullback_hom_snd _ _
    (IsPullback.of_hasPullback p (Spec.map (CommRingCat.ofHom (algebraMap k L))))

@[reassoc (attr := simp)]
theorem baseChangeTowerIso_inv_snd
    (k K L : Type u) [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra K L] [Algebra k L] [IsScalarTower k K L]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) :
    (baseChangeTowerIso k K L p).inv ≫
        pullback.snd
          (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k K))))
          (Spec.map (CommRingCat.ofHom (algebraMap K L))) =
      pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k L))) := by
  rw [Iso.inv_comp_eq, baseChangeTowerIso_hom_snd]

@[reassoc (attr := simp)]
theorem baseChangeTowerIso_inv_fst
    (k K L : Type u) [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra K L] [Algebra k L] [IsScalarTower k K L]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) :
    (baseChangeTowerIso k K L p).inv ≫
        pullback.fst
          (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k K))))
          (Spec.map (CommRingCat.ofHom (algebraMap K L))) ≫
      pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap k K))) =
        pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap k L))) := by
  rw [← cancel_epi (baseChangeTowerIso k K L p).hom]
  simp only [Iso.hom_inv_id_assoc, baseChangeTowerIso_hom_fst]

@[simp]
theorem baseChangeTowerIso_inv_appTop_fst_fst
    (k K L : Type u) [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra K L] [Algebra k L] [IsScalarTower k K L]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) (x : Γ(X, ⊤)) :
    (baseChangeTowerIso k K L p).inv.appTop
        ((pullback.fst
          (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k K))))
          (Spec.map (CommRingCat.ofHom (algebraMap K L)))).appTop
        ((pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap k K)))).appTop x)) =
      (pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap k L)))).appTop x := by
  have h := congrArg Hom.appTop (baseChangeTowerIso_inv_fst k K L p)
  simp only [Hom.comp_appTop] at h
  exact congr($h x)

/-- Transport of global sections along `baseChangeTowerIso`, as an
`L`-algebra equivalence. -/
noncomputable def globalSectionsBaseChangeTowerEquiv
    (k K L : Type u) [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra K L] [Algebra k L] [IsScalarTower k K L]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) :
    let q := pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k K)))
    letI := q.baseChangeGlobalSectionsAlgebra K L
    letI := p.baseChangeGlobalSectionsAlgebra k L
    Γ(pullback q (Spec.map (CommRingCat.ofHom (algebraMap K L))), ⊤) ≃ₐ[L]
      Γ(pullback p (Spec.map (CommRingCat.ofHom (algebraMap k L))), ⊤) := by
  let q := pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  letI := q.baseChangeGlobalSectionsAlgebra K L
  letI := p.baseChangeGlobalSectionsAlgebra k L
  let e := baseChangeTowerIso k K L p
  letI : IsIso e.inv := by dsimp [e]; infer_instance
  letI : IsIso (e.inv.app (⊤ : (pullback q
      (Spec.map (CommRingCat.ofHom (algebraMap K L)))).Opens)) := inferInstance
  exact
    { toRingEquiv := (asIso (e.inv.app (⊤ : (pullback q
          (Spec.map (CommRingCat.ofHom (algebraMap K L)))).Opens))).commRingCatIsoToRingEquiv
      commutes' r := by
        change (e.inv.appTop.hom.comp
            ((pullback.snd q (Spec.map (CommRingCat.ofHom (algebraMap K L)))).appTop.hom.comp
              (ΓSpecIso (.of L)).inv.hom)) r =
          ((pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k L)))).appTop.hom.comp
            (ΓSpecIso (.of L)).inv.hom) r
        congr 1
        rw [← RingHom.comp_assoc, ← CommRingCat.hom_comp, ← Hom.comp_appTop,
          baseChangeTowerIso_inv_snd] }

@[simp]
theorem globalSectionsBaseChangeTowerEquiv_apply
    (k K L : Type u) [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra K L] [Algebra k L] [IsScalarTower k K L]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of k))
    (x : Γ(pullback
      (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k K))))
      (Spec.map (CommRingCat.ofHom (algebraMap K L))), ⊤)) :
    let q := pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k K)))
    letI := q.baseChangeGlobalSectionsAlgebra K L
    letI := p.baseChangeGlobalSectionsAlgebra k L
    globalSectionsBaseChangeTowerEquiv k K L p x =
      (baseChangeTowerIso k K L p).inv.appTop x := by
  rfl

/-- Base change of global sections is compatible with a tower of field
extensions.  The left side performs the two extensions successively; the
right side first uses the canonical tensor cancellation and then extends
directly from `k` to `L`. -/
theorem globalSectionsBaseChangeEquiv_tower
    (k K L : Type u) [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra K L] [Algebra k L] [IsScalarTower k K L]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of k))
    [CompactSpace X] [QuasiSeparatedSpace X] :
    let q := pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k K)))
    letI : QuasiSeparatedSpace
        (pullback (C := Scheme) p (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :=
      quasiSeparatedSpace_of_quasiSeparated q
    letI := p.globalSectionsAlgebra k
    letI := p.baseChangeGlobalSectionsAlgebra k K
    letI := q.baseChangeGlobalSectionsAlgebra K L
    letI := p.baseChangeGlobalSectionsAlgebra k L
    (Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[L] L)
          (globalSectionsBaseChangeEquiv k K p)).trans
        ((globalSectionsBaseChangeEquiv K L q).trans
          (globalSectionsBaseChangeTowerEquiv k K L p)) =
      (Algebra.TensorProduct.cancelBaseChange k K L L Γ(X, ⊤)).trans
        (globalSectionsBaseChangeEquiv k L p) := by
  let q := pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  let _ : QuasiSeparatedSpace
      (pullback (C := Scheme) p (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :=
    quasiSeparatedSpace_of_quasiSeparated q
  let _ := p.globalSectionsAlgebra k
  let _ := p.baseChangeGlobalSectionsAlgebra k K
  let _ := q.baseChangeGlobalSectionsAlgebra K L
  let _ := p.baseChangeGlobalSectionsAlgebra k L
  let _ : Algebra K
      Γ(pullback p (Spec.map (CommRingCat.ofHom (algebraMap k L))), ⊤) :=
    ((algebraMap L
      Γ(pullback p (Spec.map (CommRingCat.ofHom (algebraMap k L))), ⊤)).comp
        (algebraMap K L)).toAlgebra
  let _ : IsScalarTower K L
      Γ(pullback p (Spec.map (CommRingCat.ofHom (algebraMap k L))), ⊤) :=
    .of_algebraMap_eq' rfl
  let _ : Algebra k
      Γ(pullback p (Spec.map (CommRingCat.ofHom (algebraMap k L))), ⊤) :=
    ((algebraMap K
      Γ(pullback p (Spec.map (CommRingCat.ofHom (algebraMap k L))), ⊤)).comp
        (algebraMap k K)).toAlgebra
  let _ : IsScalarTower k K
      Γ(pullback p (Spec.map (CommRingCat.ofHom (algebraMap k L))), ⊤) :=
    .of_algebraMap_eq' rfl
  apply AlgEquiv.coe_toAlgHom_injective
  apply Algebra.TensorProduct.ext_ring
  apply Algebra.TensorProduct.ext_ring
  ext x
  simp

end Scheme
end AlgebraicGeometry
