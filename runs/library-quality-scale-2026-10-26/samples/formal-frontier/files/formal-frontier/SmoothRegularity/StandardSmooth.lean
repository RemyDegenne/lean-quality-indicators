/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.RegularLocalRing.Polynomial
public import Mathlib.RingTheory.Smooth.StandardSmoothCotangent

/-!
# Regularity of standard-smooth algebras over fields

This file proves that every prime localization of a standard-smooth algebra
over a field is a regular local ring.

The proof uses a submersive presentation.  After localizing the presentation,
its conormal module retains the basis given by the defining relations.  Formal
smoothness gives an exact cotangent sequence.  Rank-nullity and the generalized
principal ideal theorem then compare the cotangent-space dimension with the
local Krull dimension.
-/

public section

open IsLocalRing
open scoped TensorProduct
open TensorProduct
open Module

namespace Algebra

universe u v w t z x

variable {K : Type u} {S : Type v} {ι : Type w} {σ : Type t}
  [Field K] [CommRing S] [Algebra K S] [Finite ι] [Finite σ]

section LocalizationCotangent

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
  (P : Extension.{z} R A) (M : Submonoid A)
  {A' : Type w} [CommRing A'] [Algebra A A'] [IsLocalization M A']
  [Algebra R A'] [IsScalarTower R A A']

private noncomputable def cotangentLocalizationEquiv :
    A' ⊗[A] P.Cotangent ≃ₗ[A'] (P.localization M : Extension R A').Cotangent := by
  let N : Submonoid P.Ring := M.comap (algebraMap P.Ring A)
  have hN : N.map (algebraMap P.Ring A) = M :=
    Submonoid.map_comap_eq_of_surjective P.algebraMap_surjective M
  letI : Algebra P.Ring A' := Algebra.compHom A' (algebraMap P.Ring A)
  let _ : IsScalarTower P.Ring A A' := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra P.Ring (P.localization M : Extension R A').Ring := by
    change Algebra P.Ring (Localization N)
    infer_instance
  letI : Algebra (Localization N) A' := by
    change Algebra (P.localization M : Extension R A').Ring A'
    infer_instance
  let _ : IsScalarTower P.Ring (Localization N) A' :=
    IsScalarTower.of_algebraMap_eq' <| by
      let hu : ∀ x : N, IsUnit (((algebraMap A A').comp (algebraMap P.Ring A)) x) :=
        fun x ↦ IsLocalization.map_units A' ⟨algebraMap P.Ring A x, x.2⟩
      change (algebraMap A A').comp (algebraMap P.Ring A) =
        (IsLocalization.lift
          (M := N)
          (g := (algebraMap A A').comp (algebraMap P.Ring A))
          hu).comp
            (algebraMap P.Ring (Localization N))
      exact (IsLocalization.lift_comp hu).symm
  let _ : Module (Localization N) (P.localization M : Extension R A').ker := by
    change Module (P.localization M : Extension R A').Ring
      (P.localization M : Extension R A').ker
    infer_instance
  let _ : IsScalarTower P.Ring (Localization N)
      (P.localization M : Extension R A').ker := by
    change IsScalarTower P.Ring (P.localization M : Extension R A').Ring
      (P.localization M : Extension R A').ker
    infer_instance
  let g : P.ker →ₗ[P.Ring] (P.localization M : Extension R A').ker :=
    RingHom.toKerIsLocalization (Localization N) A' (algebraMap P.Ring A)
      (hN.symm ▸ Submonoid.le_comap_map N)
  let _ : IsLocalizedModule N g := by
    exact RingHom.toKerIsLocalization_isLocalizedModule A'
      (algebraMap P.Ring A) hN
  let hbc : IsBaseChange (Localization N) g :=
    IsLocalizedModule.isBaseChange N (Localization N) g
  let e : A' ⊗[Localization N] (P.localization M : Extension R A').ker ≃ₗ[A']
      (P.localization M : Extension R A').Cotangent := by
    change A' ⊗[(P.localization M : Extension R A').Ring]
      (P.localization M : Extension R A').ker ≃ₗ[A']
        (P.localization M : Extension R A').Cotangent
    exact (P.localization M).cotangentEquiv
  exact
    (P.cotangentEquiv.symm.baseChange A A').trans
      ((AlgebraTensorModule.cancelBaseChange P.Ring A A' A' P.ker).trans
        ((AlgebraTensorModule.cancelBaseChange P.Ring (Localization N) A' A' P.ker).symm.trans
          ((AlgebraTensorModule.congr (.refl A' A') hbc.equiv).trans e)))

end LocalizationCotangent

section LocalizedSubmersiveCotangent

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
  (P : SubmersivePresentation R A ι σ) (M : Submonoid A)
  {A' : Type x} [CommRing A'] [Algebra A A'] [IsLocalization M A']
  [Algebra R A'] [IsScalarTower R A A']

private noncomputable def localizedCotangentBasis :
    Basis σ A' (P.toExtension.localization M : Extension R A').Cotangent :=
  (P.basisCotangent.baseChange A').map
    (cotangentLocalizationEquiv P.toExtension M)

end LocalizedSubmersiveCotangent

section ExtensionLocalCotangent

variable {R : Type u} {B : Type v} [CommRing R] [CommRing B] [Algebra R B]
  (P : Extension.{z} R B) [IsLocalRing P.Ring] [IsLocalRing B]

private lemma Extension.cotangent_finrank_eq_of_formallySmooth
    [FormallySmooth R P.Ring] [FormallySmooth R B]
    [IsNoetherianRing P.Ring] [IsNoetherianRing B]
    (b : Basis σ B P.Cotangent) :
    Nat.card σ + Module.finrank (ResidueField B) (IsLocalRing.CotangentSpace B) =
      Module.finrank (ResidueField P.Ring) (IsLocalRing.CotangentSpace P.Ring) := by
  let _ : IsLocalHom (algebraMap P.Ring B) :=
    IsLocalHom.of_surjective (algebraMap P.Ring B) P.algebraMap_surjective
  have hker : P.ker ≤ maximalIdeal P.Ring := by
    rw [← IsLocalRing.maximalIdeal_comap (algebraMap P.Ring B)]
    intro x hx
    simp [RingHom.mem_ker.mp hx]
  let ψ : B →+* ResidueField P.Ring :=
    (algebraMap P.Ring B).liftOfSurjective P.algebraMap_surjective
      ⟨residue P.Ring, by simpa [IsLocalRing.ker_residue] using hker⟩
  let _ : Algebra B (ResidueField P.Ring) := ψ.toAlgebra
  let _ : IsScalarTower P.Ring B (ResidueField P.Ring) :=
    IsScalarTower.of_algebraMap_eq' <| by
      change residue P.Ring = ψ.comp (algebraMap P.Ring B)
      exact (RingHom.liftOfSurjective_comp (algebraMap P.Ring B)
        P.algebraMap_surjective
          ⟨residue P.Ring, by simpa [IsLocalRing.ker_residue] using hker⟩).symm
  let _ : Module B (IsLocalRing.CotangentSpace P.Ring) :=
    Module.compHom (IsLocalRing.CotangentSpace P.Ring) (algebraMap B (ResidueField P.Ring))
  let _ : IsScalarTower B (ResidueField P.Ring) (IsLocalRing.CotangentSpace P.Ring) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let _ : IsScalarTower P.Ring B (IsLocalRing.CotangentSpace P.Ring) :=
    IsScalarTower.of_algebraMap_smul fun r x ↦ by
      change ψ (algebraMap P.Ring B r) • x = residue P.Ring r • x
      rw [show ψ (algebraMap P.Ring B r) = residue P.Ring r by
        exact RingHom.liftOfSurjective_comp_apply (algebraMap P.Ring B)
          P.algebraMap_surjective
            ⟨residue P.Ring, by simpa [IsLocalRing.ker_residue] using hker⟩ r]
  let raw : P.Cotangent →ₗ[P.Ring] IsLocalRing.CotangentSpace P.Ring :=
    (Ideal.mapCotangent P.ker (maximalIdeal P.Ring) (Algebra.ofId P.Ring P.Ring) hker).comp
      P.cotangentEquivCotangentKer.toLinearMap
  let rel : P.Cotangent →ₗ[B] IsLocalRing.CotangentSpace P.Ring :=
    raw.extendScalarsOfSurjective P.algebraMap_surjective
  let relBase : (ResidueField P.Ring) ⊗[B] P.Cotangent →ₗ[ResidueField P.Ring]
      IsLocalRing.CotangentSpace P.Ring :=
    rel.liftBaseChange (ResidueField P.Ring)
  have hmax : (maximalIdeal B).comap (algebraMap P.Ring B) = maximalIdeal P.Ring :=
    IsLocalRing.maximalIdeal_comap (algebraMap P.Ring B)
  have hmapEq : (maximalIdeal B).comap (algebraMap P.Ring B) =
      P.ker ⊔ maximalIdeal P.Ring :=
    hmax.trans (sup_eq_right.mpr hker).symm
  let hle : maximalIdeal P.Ring ≤
      (maximalIdeal B).comap (algebraMap P.Ring B) :=
    le_of_le_of_eq le_sup_right hmapEq.symm
  let mapcot := Ideal.mapCotangent (maximalIdeal P.Ring) (maximalIdeal B)
    (Algebra.ofId P.Ring B) hle
  let _ : Module (ResidueField P.Ring) (IsLocalRing.CotangentSpace B) :=
    Module.compHom (IsLocalRing.CotangentSpace B)
      (algebraMap (ResidueField P.Ring) (ResidueField B))
  let _ : IsScalarTower (ResidueField P.Ring) (ResidueField B) (IsLocalRing.CotangentSpace B) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let _ : IsScalarTower P.Ring B (IsLocalRing.CotangentSpace B) := by infer_instance
  let _ : IsScalarTower B (ResidueField P.Ring) (IsLocalRing.CotangentSpace B) := by
    apply IsScalarTower.of_algebraMap_smul
    intro b x
    obtain ⟨r, rfl⟩ := P.algebraMap_surjective b
    have hr : algebraMap (ResidueField P.Ring) (ResidueField B)
        (ψ (algebraMap P.Ring B r)) = residue B (algebraMap P.Ring B r) := by
      rw [show ψ (algebraMap P.Ring B r) = residue P.Ring r by
        exact RingHom.liftOfSurjective_comp_apply (algebraMap P.Ring B)
          P.algebraMap_surjective
            ⟨residue P.Ring, by simpa [IsLocalRing.ker_residue] using hker⟩ r]
      exact IsLocalRing.ResidueField.algebraMap_residue r
    calc
      (algebraMap B (ResidueField P.Ring) (algebraMap P.Ring B r)) • x =
          (algebraMap (ResidueField P.Ring) (ResidueField B)
            (ψ (algebraMap P.Ring B r))) • x := rfl
      _ = (residue B (algebraMap P.Ring B r)) • x :=
        congrArg (fun a : ResidueField B ↦ a • x) hr
      _ = (algebraMap B (ResidueField B) (algebraMap P.Ring B r)) • x := rfl
      _ = (algebraMap P.Ring B r) • x :=
        IsScalarTower.algebraMap_smul (A := ResidueField B) (algebraMap P.Ring B r) x
  let _ : IsScalarTower P.Ring (ResidueField P.Ring) (IsLocalRing.CotangentSpace B) := by
    apply IsScalarTower.of_algebraMap_smul
    intro r x
    have hr : algebraMap (ResidueField P.Ring) (ResidueField B) (residue P.Ring r) =
        residue B (algebraMap P.Ring B r) :=
      IsLocalRing.ResidueField.algebraMap_residue r
    calc
      (algebraMap P.Ring (ResidueField P.Ring) r) • x =
          (algebraMap (ResidueField P.Ring) (ResidueField B)
            (residue P.Ring r)) • x := rfl
      _ = (residue B (algebraMap P.Ring B r)) • x :=
        congrArg (fun a : ResidueField B ↦ a • x) hr
      _ = (algebraMap B (ResidueField B) (algebraMap P.Ring B r)) • x := rfl
      _ = (algebraMap P.Ring B r) • x :=
        IsScalarTower.algebraMap_smul (A := ResidueField B) (algebraMap P.Ring B r) x
      _ = r • x := IsScalarTower.algebraMap_smul (A := B) r x
  let localMap : IsLocalRing.CotangentSpace P.Ring →ₗ[ResidueField P.Ring]
      IsLocalRing.CotangentSpace B :=
    mapcot.extendScalarsOfSurjective (residue_surjective (R := P.Ring))
  have hsurj : Function.Surjective localMap :=
    Ideal.mapCotangent_surjective_of_comap_eq P.algebraMap_surjective hmapEq
  have hcomp : localMap ∘ₗ relBase = 0 := by
    apply AlgebraTensorModule.ext
    intro a x
    obtain ⟨x, rfl⟩ := Extension.Cotangent.mk_surjective (P := P) x
    have hmap :
        (mapcot.extendScalarsOfSurjective (residue_surjective (R := P.Ring)))
          ((maximalIdeal P.Ring).toCotangent ⟨x, hker x.2⟩) = 0 := by
      change (maximalIdeal B).toCotangent
        ⟨algebraMap P.Ring B x, hle (hker x.2)⟩ = 0
      convert map_zero (maximalIdeal B).toCotangent
      exact SetCoe.ext (RingHom.mem_ker.mp x.2)
    simp [localMap, mapcot, relBase, rel, raw, LinearMap.liftBaseChange_tmul,
      Ideal.mapCotangent_toCotangent, Extension.Cotangent.val_mk, hmap]
  have hrange : LinearMap.range relBase = LinearMap.ker localMap := by
    apply le_antisymm
    · rintro y ⟨x, rfl⟩
      rw [LinearMap.mem_ker]
      exact DFunLike.congr_fun hcomp x
    · intro y hy
      have hy' : y ∈ LinearMap.ker mapcot := by
        rw [LinearMap.mem_ker] at hy ⊢
        exact hy
      rw [Ideal.mapCotangent_ker_of_surjective P.algebraMap_surjective hmapEq] at hy'
      obtain ⟨x, hx, rfl⟩ := hy'
      let z : P.ker := ⟨x, (Ideal.mem_inf.mp hx).1⟩
      refine ⟨1 ⊗ₜ[B] Extension.Cotangent.mk z, ?_⟩
      simp [relBase, rel, raw, LinearMap.liftBaseChange_tmul,
        Extension.Cotangent.val_mk, z]
  have hinjComplex : Function.Injective
      (P.cotangentComplex.lTensor (ResidueField P.Ring)) := by
    obtain ⟨l, hl⟩ := P.formallySmooth_iff_split_injection.mp
      (inferInstance : FormallySmooth R B)
    apply_fun (LinearMap.lTensor (ResidueField P.Ring)) at hl
    rw [LinearMap.lTensor_comp, LinearMap.lTensor_id] at hl
    exact Function.HasLeftInverse.injective ⟨l.lTensor (ResidueField P.Ring),
      DFunLike.congr_fun hl⟩
  let hres : RingHom.ker (algebraMap P.Ring (ResidueField P.Ring)) =
      maximalIdeal P.Ring := by
    rw [IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.ker_residue]
  let sourceToDiffRaw : IsLocalRing.CotangentSpace P.Ring →ₗ[P.Ring]
      (ResidueField P.Ring) ⊗[P.Ring] Ω[P.Ring⁄R] :=
    (KaehlerDifferential.kerCotangentToTensor R P.Ring (ResidueField P.Ring)).comp
      (Ideal.Cotangent.equivOfEq _ _ hres.symm).toLinearMap
  let sourceToDiff : IsLocalRing.CotangentSpace P.Ring →ₗ[ResidueField P.Ring]
      (ResidueField P.Ring) ⊗[P.Ring] Ω[P.Ring⁄R] :=
    sourceToDiffRaw.extendScalarsOfSurjective (residue_surjective (R := P.Ring))
  let toDiff : IsLocalRing.CotangentSpace P.Ring →ₗ[ResidueField P.Ring]
      (ResidueField P.Ring) ⊗[B] P.CotangentSpace :=
    (AlgebraTensorModule.cancelBaseChange P.Ring B (ResidueField P.Ring)
      (ResidueField P.Ring) Ω[P.Ring⁄R]).symm.toLinearMap.comp sourceToDiff
  have sourceToDiff_toCotangent (x : maximalIdeal P.Ring) :
      sourceToDiff ((maximalIdeal P.Ring).toCotangent x) =
        1 ⊗ₜ[P.Ring] KaehlerDifferential.D R P.Ring x := by
    change sourceToDiffRaw ((maximalIdeal P.Ring).toCotangent x) = _
    change ((KaehlerDifferential.kerCotangentToTensor R P.Ring
      (ResidueField P.Ring)).comp
        (Ideal.Cotangent.equivOfEq _ _ hres.symm).toLinearMap)
          ((maximalIdeal P.Ring).toCotangent x) = _
    rw [LinearMap.comp_apply]
    change (KaehlerDifferential.kerCotangentToTensor R P.Ring
      (ResidueField P.Ring))
        ((Ideal.Cotangent.equivOfEq _ _ hres.symm)
          ((maximalIdeal P.Ring).toCotangent x)) = _
    rw [
      Ideal.Cotangent.equivOfEq_toCotangent,
      KaehlerDifferential.kerCotangentToTensor_toCotangent]
    rfl
  have hdiff : toDiff ∘ₗ relBase =
      P.cotangentComplex.lTensor (ResidueField P.Ring) := by
    apply AlgebraTensorModule.ext
    intro a x
    obtain ⟨x, rfl⟩ := Extension.Cotangent.mk_surjective (P := P) x
    simp [toDiff, relBase, rel, raw,
      LinearMap.liftBaseChange_tmul, LinearMap.lTensor_tmul,
      Extension.Cotangent.val_mk, Extension.cotangentComplex_mk,
      sourceToDiff_toCotangent]
    simp [TensorProduct.smul_tmul']
  have hinjRelBase : Function.Injective relBase := by
    intro x y hxy
    apply hinjComplex
    rw [← hdiff]
    exact congrArg toDiff hxy
  have hresidueBij : Function.Bijective
      (algebraMap (ResidueField P.Ring) (ResidueField B)) := by
    refine ⟨RingHom.injective _, ?_⟩
    intro y
    obtain ⟨b, rfl⟩ := residue_surjective y
    obtain ⟨r, rfl⟩ := P.algebraMap_surjective b
    exact ⟨residue P.Ring r, IsLocalRing.ResidueField.algebraMap_residue r⟩
  have hfinCotangent :
      Module.finrank (ResidueField P.Ring) (IsLocalRing.CotangentSpace B) =
        Module.finrank (ResidueField B) (IsLocalRing.CotangentSpace B) := by
    rw [← Module.finrank_mul_finrank (ResidueField P.Ring) (ResidueField B)
      (IsLocalRing.CotangentSpace B), Module.finrank_of_bijective_algebraMap hresidueBij, one_mul]
  have hdimExact :
      Module.finrank (ResidueField P.Ring)
          ((ResidueField P.Ring) ⊗[B] P.Cotangent) +
        Module.finrank (ResidueField P.Ring) (IsLocalRing.CotangentSpace B) =
          Module.finrank (ResidueField P.Ring) (IsLocalRing.CotangentSpace P.Ring) := by
    rw [← LinearMap.finrank_range_of_inj hinjRelBase]
    calc
      _ = Module.finrank (ResidueField P.Ring) (LinearMap.ker localMap) +
          Module.finrank (ResidueField P.Ring) (LinearMap.range localMap) := by
        rw [← hrange, show LinearMap.range localMap = ⊤ from
          LinearMap.range_eq_top.mpr hsurj, finrank_top]
      _ = _ := by
        rw [add_comm, LinearMap.finrank_range_add_finrank_ker]
  let _ := Fintype.ofFinite σ
  have hfinRel :
      Module.finrank (ResidueField P.Ring)
          ((ResidueField P.Ring) ⊗[B] P.Cotangent) = Nat.card σ := by
    rw [Module.finrank_eq_card_basis (b.baseChange (ResidueField P.Ring)),
      Nat.card_eq_fintype_card]
  rwa [hfinRel, hfinCotangent] at hdimExact

end ExtensionLocalCotangent

section RegularOfCotangentBound

variable {R : Type u} {B : Type v} [CommRing R] [CommRing B] [Algebra R B]
  (P : Extension.{z} R B) [IsLocalRing B]
  [IsLocalHom (algebraMap P.Ring B)] [IsNoetherianRing B]
  [IsRegularLocalRing P.Ring]

private lemma isRegularLocalRing_of_spanFinrank_add_finrank_cotangentSpace_le
    (h : P.ker.spanFinrank +
        Module.finrank (ResidueField B) (IsLocalRing.CotangentSpace B) ≤
      Module.finrank (ResidueField P.Ring) (IsLocalRing.CotangentSpace P.Ring)) :
    IsRegularLocalRing B := by
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  rw [IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
  have hregular :
      (Module.finrank (ResidueField P.Ring) (IsLocalRing.CotangentSpace P.Ring) : WithBot ENat) =
        ringKrullDim P.Ring :=
    (IsRegularLocalRing.iff_finrank_cotangentSpace P.Ring).mp inferInstance
  have hker : P.ker ≤ Ring.jacobson P.Ring := by
    rw [IsLocalRing.ringJacobson_eq_maximalIdeal]
    rw [← IsLocalRing.maximalIdeal_comap (algebraMap P.Ring B)]
    intro x hx
    simp [RingHom.mem_ker.mp hx]
  have hdim := ringKrullDim_le_ringKrullDim_quotient_add_spanFinrank P.ker hker
  rw [ringKrullDim_eq_of_ringEquiv
    (RingHom.quotientKerEquivOfSurjective P.algebraMap_surjective)] at hdim
  rw [← hregular] at hdim
  have hcast :
      (P.ker.spanFinrank : WithBot ENat) +
          Module.finrank (ResidueField B) (IsLocalRing.CotangentSpace B) ≤
        (P.ker.spanFinrank : WithBot ENat) + ringKrullDim B := by
    calc
      _ = ((P.ker.spanFinrank +
          Module.finrank (ResidueField B) (IsLocalRing.CotangentSpace B) : ℕ) : WithBot ENat) := by
        norm_num
      _ ≤ Module.finrank (ResidueField P.Ring) (IsLocalRing.CotangentSpace P.Ring) := by
        exact_mod_cast h
      _ ≤ ringKrullDim B + P.ker.spanFinrank := hdim
      _ = _ := add_comm _ _
  exact ENat.WithBot.add_le_add_natCast_left_iff.mp hcast

end RegularOfCotangentBound

private noncomputable abbrev localizedExtension
    (P : SubmersivePresentation K S ι σ) (q : Ideal S) [q.IsPrime] :
    Extension K (Localization.AtPrime q) :=
  P.toExtension.localization q.primeCompl

private lemma localizedExtension_isRegularLocalRing
    (P : SubmersivePresentation K S ι σ) (q : Ideal S) [q.IsPrime] :
    IsRegularLocalRing (localizedExtension P q).Ring := by
  change IsRegularLocalRing
    (Localization.AtPrime (q.comap (algebraMap P.Ring S)))
  infer_instance

omit [Finite ι] in
private lemma localizedExtension_ker_eq_map
    (P : SubmersivePresentation K S ι σ) (q : Ideal S) [q.IsPrime] :
    (localizedExtension P q).ker =
      P.toExtension.ker.map
        (algebraMap P.Ring
          (Localization (q.primeCompl.comap (algebraMap P.Ring S)))) := by
  let hM : Submonoid.map (algebraMap P.Ring S)
      (q.primeCompl.comap (algebraMap P.Ring S)) = q.primeCompl :=
    Submonoid.map_comap_eq_of_surjective P.algebraMap_surjective q.primeCompl
  exact IsLocalization.ker_map
    (S := Localization (q.primeCompl.comap (algebraMap P.Ring S)))
    (Localization.AtPrime q) (algebraMap P.Ring S) hM

omit [Finite ι] in
private lemma localizedExtension_ker_spanFinrank_le_card
    (P : SubmersivePresentation K S ι σ) (q : Ideal S) [q.IsPrime] :
    (localizedExtension P q).ker.spanFinrank ≤ Nat.card σ := by
  rw [localizedExtension_ker_eq_map P q]
  refine (Ideal.spanFinrank_map_le_of_fg _ ?_).trans ?_
  · change P.ker.FG
    rw [← P.span_range_relation_eq_ker]
    exact Submodule.fg_span (Set.finite_range _)
  · change P.ker.spanFinrank ≤ Nat.card σ
    rw [← P.span_range_relation_eq_ker]
    refine (Submodule.spanFinrank_span_le_ncard_of_finite
      (Set.finite_range _)).trans ?_
    rw [← Nat.card_coe_set_eq]
    exact Finite.card_range_le P.relation

private lemma SubmersivePresentation.isRegularLocalRing_atPrime
    (P : SubmersivePresentation K S ι σ) (q : Ideal S) [q.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime q) := by
  let E := localizedExtension P q
  let _ : IsStandardSmooth K S := P.isStandardSmooth
  let _ : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing K S
  let _ : IsRegularLocalRing E.Ring := localizedExtension_isRegularLocalRing P q
  let _ : FormallySmooth K E.Ring := by
    change FormallySmooth K
      (Localization (q.primeCompl.comap (algebraMap P.Ring S)))
    infer_instance
  let _ : IsLocalHom (algebraMap E.Ring (Localization.AtPrime q)) :=
    IsLocalHom.of_surjective _ E.algebraMap_surjective
  have hdim :
      Nat.card σ + Module.finrank (ResidueField (Localization.AtPrime q))
          (IsLocalRing.CotangentSpace (Localization.AtPrime q)) =
        Module.finrank (ResidueField E.Ring) (IsLocalRing.CotangentSpace E.Ring) :=
    Extension.cotangent_finrank_eq_of_formallySmooth E
      (localizedCotangentBasis P q.primeCompl
        (A' := Localization.AtPrime q))
  apply isRegularLocalRing_of_spanFinrank_add_finrank_cotangentSpace_le E
  exact (Nat.add_le_add_right (localizedExtension_ker_spanFinrank_le_card P q) _).trans_eq hdim

/-- Every prime localization of a standard-smooth algebra over a field is a
regular local ring. -/
theorem IsStandardSmooth.isRegularLocalRing_atPrime
    {K : Type u} {S : Type v} [Field K] [CommRing S] [Algebra K S]
    [IsStandardSmooth K S] (q : Ideal S) [q.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime q) := by
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := ‹IsStandardSmooth K S›
  exact P.isRegularLocalRing_atPrime q

end Algebra
