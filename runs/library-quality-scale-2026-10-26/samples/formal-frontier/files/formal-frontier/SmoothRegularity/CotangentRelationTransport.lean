/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SmoothRegularity.AlgClosed
public import SmoothRegularity.CotangentRelations

/-!
# Transporting presentation relations to local cotangent spaces

This file transports a minimal family of presentation relations from the
base-changed cotangent kernel to literal cotangent classes in the localization
of the presentation ring at the prime over a closed point.

The proof compares the two residue fields, cancels the intermediate scalar
extension, and uses the split-residue description of the local cotangent
space. It does not assert that a quotient by the selected relations is regular
or a complete intersection.
-/

public section

open scoped TensorProduct

namespace Algebra.Presentation

universe u v

variable {K : Type u} [Field K] [IsAlgClosed K]
variable {S : Type v} [CommRing S] [Algebra K S] [Algebra.FiniteType K S]

omit [IsAlgClosed K] in
private lemma conormalEquiv_apply {R : Type v}
    [CommRing R] [IsLocalRing R] [Algebra K R]
    (e : IsLocalRing.ResidueField R ≃ₐ[K] K)
    (x : IsLocalRing.maximalIdeal R) :
    IsLocalRing.cotangentSpaceEquivTensorKaehlerOfResidueEquiv e
        ((IsLocalRing.maximalIdeal R).toCotangent x) =
      1 ⊗ₜ[R] KaehlerDifferential.D K R x.1 := by
  exact IsLocalRing.cotangentSpaceEquivTensorKaehlerOfResidueEquiv_apply_toCotangent e x

/-- At a maximal prime over a closed point, select a minimal family of
presentation relations whose literal classes in the localized cotangent space
are linearly independent. The result also returns the membership proof needed
to form each cotangent class. -/
theorem exists_relations_linearIndependent_localCotangent {n r : ℕ}
    (P : Algebra.Presentation K S (Fin n) (Fin r))
    (m : Ideal S) [m.IsMaximal]
    (q : Ideal P.toExtension.Ring) [q.IsMaximal]
    (hq : q = m.comap (algebraMap P.toExtension.Ring S)) :
    ∃ f : Fin (Module.finrank m.ResidueField
        (LinearMap.ker (P.toExtension.toKaehler.baseChange m.ResidueField))) → Fin r,
      ∃ hrel : ∀ i, P.relation (f i) ∈ q,
        LinearIndependent q.ResidueField (fun i ↦
          (IsLocalRing.maximalIdeal (Localization.AtPrime q)).toCotangent
            ⟨algebraMap P.toExtension.Ring (Localization.AtPrime q)
                (P.relation (f i)),
              (IsLocalization.AtPrime.to_map_mem_maximal_iff
                (Localization.AtPrime q) q (P.relation (f i))).mpr (hrel i)⟩) := by
  let _ : IsScalarTower P.toExtension.Ring S m.ResidueField :=
    IsScalarTower.of_algebraMap_eq' (by rfl)
  let rhoRing : q.ResidueField →+* m.ResidueField :=
    Ideal.ResidueField.map q m (algebraMap P.toExtension.Ring S) hq
  let rho : q.ResidueField →ₐ[P.toExtension.Ring] m.ResidueField :=
    { rhoRing with
      commutes' := fun x ↦ by
        change (Ideal.ResidueField.map q m (algebraMap P.toExtension.Ring S) hq)
          (algebraMap P.toExtension.Ring q.ResidueField x) = _
        rw [Ideal.ResidueField.map_algebraMap]
        exact IsScalarTower.algebraMap_apply
          P.toExtension.Ring S m.ResidueField x }
  have hrho : Function.Bijective rho := by
    apply RingHom.SurjectiveOnStalks.residueFieldMap_bijective
    exact RingHom.surjectiveOnStalks_of_surjective
      P.toExtension.algebraMap_surjective
  let erho : q.ResidueField ≃ₐ[P.toExtension.Ring] m.ResidueField :=
    AlgEquiv.ofBijective rho hrho
  let cancel : m.ResidueField ⊗[S] P.toExtension.CotangentSpace ≃ₗ[S]
      m.ResidueField ⊗[P.toExtension.Ring] Ω[P.toExtension.Ring⁄K] :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange
      P.toExtension.Ring S S m.ResidueField Ω[P.toExtension.Ring⁄K]
  let residueChange : m.ResidueField ⊗[P.toExtension.Ring]
      Ω[P.toExtension.Ring⁄K] ≃ₗ[P.toExtension.Ring]
      q.ResidueField ⊗[P.toExtension.Ring] Ω[P.toExtension.Ring⁄K] :=
    TensorProduct.AlgebraTensorModule.congr erho.symm.toLinearEquiv
      (LinearEquiv.refl P.toExtension.Ring Ω[P.toExtension.Ring⁄K])
  let toTensor : m.ResidueField ⊗[S] P.toExtension.CotangentSpace ≃ₗ[K]
      q.ResidueField ⊗[P.toExtension.Ring] Ω[P.toExtension.Ring⁄K] :=
    (cancel.restrictScalars K).trans (residueChange.restrictScalars K)
  have hcotangentComplex (j : Fin r) :
      P.toExtension.cotangentComplex
          (Algebra.Extension.Cotangent.mk
            ⟨P.relation j, P.relation_mem_ker j⟩) =
        1 ⊗ₜ[P.toExtension.Ring]
          KaehlerDifferential.D K P.toExtension.Ring (P.relation j) := by
    rfl
  have htoTensor (j : Fin r) :
      toTensor ((P.toExtension.cotangentComplex.baseChange m.ResidueField)
          (1 ⊗ₜ[S] Algebra.Extension.Cotangent.mk
            ⟨P.relation j, P.relation_mem_ker j⟩)) =
        1 ⊗ₜ[P.toExtension.Ring]
          KaehlerDifferential.D K P.toExtension.Ring (P.relation j) := by
    dsimp only [toTensor]
    rw [LinearEquiv.trans_apply]
    change residueChange (cancel _) = _
    rw [LinearMap.baseChange_tmul, hcotangentComplex,
      TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
      TensorProduct.AlgebraTensorModule.congr_tmul]
    simp
  obtain ⟨f, _hspan, hli⟩ :=
    P.exists_relations_spanning_cotangentKernel m
  have hliK : LinearIndependent K (fun i ↦
      (P.toExtension.cotangentComplex.baseChange m.ResidueField)
        (1 ⊗ₜ[S] Algebra.Extension.Cotangent.mk
          ⟨P.relation (f i), P.relation_mem_ker (f i)⟩)) :=
    hli.restrict_scalars' K
  have hliTensorK : LinearIndependent K (fun i ↦
      (1 : q.ResidueField) ⊗ₜ[P.toExtension.Ring]
        KaehlerDifferential.D K P.toExtension.Ring (P.relation (f i))) := by
    have hmap := hliK.map' toTensor.toLinearMap
      (LinearMap.ker_eq_bot.mpr toTensor.injective)
    change LinearIndependent K (fun i ↦ toTensor
      ((P.toExtension.cotangentComplex.baseChange m.ResidueField)
        (1 ⊗ₜ[S] Algebra.Extension.Cotangent.mk
          ⟨P.relation (f i), P.relation_mem_ker (f i)⟩))) at hmap
    simpa only [htoTensor] using hmap
  let e : q.ResidueField ≃ₐ[K] K :=
    (erho.restrictScalars K).trans
      (m.residueFieldAlgEquivOfIsAlgClosed (K := K))
  have hKsurj : Function.Surjective (algebraMap K q.ResidueField) := by
    intro x
    refine ⟨e x, ?_⟩
    apply e.injective
    simp [e]
  have hliTensor : LinearIndependent q.ResidueField (fun i ↦
      (1 : q.ResidueField) ⊗ₜ[P.toExtension.Ring]
        KaehlerDifferential.D K P.toExtension.Ring (P.relation (f i))) := by
    have hmap := hliTensorK.map_of_surjective_injectiveₛ
      (algebraMap K q.ResidueField) (AddMonoidHom.id _)
      hKsurj Function.injective_id (fun k x ↦ by
        exact (IsScalarTower.algebraMap_smul q.ResidueField k x).symm)
    change LinearIndependent q.ResidueField (fun i ↦
      AddMonoidHom.id _ ((1 : q.ResidueField) ⊗ₜ[P.toExtension.Ring]
        KaehlerDifferential.D K P.toExtension.Ring (P.relation (f i)))) at hmap
    simpa only [AddMonoidHom.id_apply] using hmap
  let localE : IsLocalRing.CotangentSpace (Localization.AtPrime q) ≃ₗ[q.ResidueField]
      q.ResidueField ⊗[P.toExtension.Ring] Ω[P.toExtension.Ring⁄K] :=
    (IsLocalRing.cotangentSpaceEquivTensorKaehlerOfResidueEquiv e).trans <|
      ((KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale
        K P.toExtension.Ring (Localization.AtPrime q)).symm.baseChange
          (Localization.AtPrime q) q.ResidueField _ _).trans <|
        TensorProduct.AlgebraTensorModule.cancelBaseChange P.toExtension.Ring
          (Localization.AtPrime q) q.ResidueField q.ResidueField
          Ω[P.toExtension.Ring⁄K]
  have hlocalE (x : P.toExtension.Ring) (hx : x ∈ q) :
      localE ((IsLocalRing.maximalIdeal (Localization.AtPrime q)).toCotangent
        ⟨algebraMap P.toExtension.Ring (Localization.AtPrime q) x,
          (IsLocalization.AtPrime.to_map_mem_maximal_iff
            (Localization.AtPrime q) q x).mpr hx⟩) =
        (1 : q.ResidueField) ⊗ₜ[P.toExtension.Ring]
          KaehlerDifferential.D K P.toExtension.Ring x := by
    dsimp only [localE]
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, conormalEquiv_apply,
      LinearEquiv.baseChange_tmul,
      KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap,
      TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
    simp only [one_smul]
  have hrelq (j : Fin r) : P.relation j ∈ q := by
    rw [hq]
    change algebraMap P.toExtension.Ring S (P.relation j) ∈ m
    rw [show algebraMap P.toExtension.Ring S (P.relation j) = 0 from
      P.relation_mem_ker j]
    exact m.zero_mem
  have hliLocal : LinearIndependent q.ResidueField (fun i ↦
      (IsLocalRing.maximalIdeal (Localization.AtPrime q)).toCotangent
        ⟨algebraMap P.toExtension.Ring (Localization.AtPrime q)
            (P.relation (f i)),
          (IsLocalization.AtPrime.to_map_mem_maximal_iff
            (Localization.AtPrime q) q (P.relation (f i))).mpr
              (hrelq (f i))⟩) := by
    have hmap := hliTensor.map' localE.symm.toLinearMap
      (LinearMap.ker_eq_bot.mpr localE.symm.injective)
    change LinearIndependent q.ResidueField (fun i ↦ localE.symm
      ((1 : q.ResidueField) ⊗ₜ[P.toExtension.Ring]
        KaehlerDifferential.D K P.toExtension.Ring (P.relation (f i)))) at hmap
    convert hmap using 1
    funext i
    apply localE.injective
    rw [localE.apply_symm_apply]
    exact hlocalE (P.relation (f i)) (hrelq (f i))
  refine ⟨f, fun i ↦ hrelq (f i), ?_⟩
  convert hliLocal using 1

end Algebra.Presentation
