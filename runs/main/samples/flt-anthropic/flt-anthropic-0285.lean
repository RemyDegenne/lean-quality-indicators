namespace P2MW.S_ModularCurve_FullLevel_exists_reads_resAut_smul_and_centred_iff_of_mem_closure_levelAutBar_twoChartIntegralModel_of_eq_three

attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

universe u

p2m_open

section FTW5

p2m_open

open scoped MatrixGroups

namespace TH1Wanted2

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

theorem inv_mem_and_const_mem_of_gaussPresentation
    (q : ℕ) [Fact q.Prime] (hq3 : q = 3) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ))
    (K₁ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (hK₁ : FiniteDimensional ↥k₀ ↥K₁)
    (A₁ : ValuationSubring ↥K₁) (hA₁ : ∀ x : ↥K₁, x ∈ A₁ ↔ (x : AlgebraicClosure ℚ) ∈ A) :
    letI : Algebra ↥k₀ ↥(fieldBar q M') :=
      ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra
    ∀ (F₀ : IntermediateField ↥k₀ ↥(fieldBar q M')),
      (IntermediateField.adjoin ↥k₀ (Set.range (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M'))) ⊔ F₀ = ⊤) →
      (∀ (K' : IntermediateField ↥k₀ (AlgebraicClosure ℚ)), FiniteDimensional ↥k₀ ↥K' →
        ∀ (m : ℕ) (c : Fin m → AlgebraicClosure ℚ) (a : Fin m → ↥(fieldBar q M')), (∀ i, a i ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K' : Set (AlgebraicClosure ℚ))) ⊔ F₀) →
          LinearIndependent ↥K' c → ∑ i, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (c i) * a i = 0 → ∀ i, a i = 0) →
      (∀ f : ↥(fieldBar q M'), (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ Set.range ⇑(coeffEmb (AlgebraicClosure ℚ)) → f ∈ F₀) →
    ∀ [Algebra ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)],
      (∀ a : ↥A₁, ((algebraMap ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) a : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) =
        algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥K₁) : AlgebraicClosure ℚ)) →
    ∀ (j₁ : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)),
      ((j₁ : ↥(fieldBar q M')) = IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M'))) →
    ∀ [Fact (j₁ ≠ 0)],
    ∀ (j' : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)),
      ((j' : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ q jq) →
    ∀ (O : ValuationSubring ↥(fieldBar q M')),
      (∀ f : ↥(fieldBar q M'), f ∈ O ↔
        ∃ x y : LaurentSeries ↥A, coeffMap (IsLocalRing.residue ↥A) y ≠ 0 ∧
          (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x) →
    ((j₁ : ↥(fieldBar q M')))⁻¹ ∈ O ∧ (j₁ : ↥(fieldBar q M')) ∈ O ∧
    ((j' : ↥(fieldBar q M')))⁻¹ ∈ O ∧ (j' : ↥(fieldBar q M')) ∈ O ∧
    (∀ a : ↥A₁, ((algebraMap ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) a : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) ∈ O) := by
  classical
  intro F₀ hK1 hLD hRAT instA₁ halg j₁ hj₁ instj₁ j' hj' O hO
  have hjt0 : (j₁ : ↥(fieldBar q M')) ≠ 0 := fun h => (Fact.out : j₁ ≠ 0) (Subtype.ext h)
  have hcoej₁ : ((j₁ : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) jq := by
    rw [hj₁]; rfl
  have hjq : coeffEmb (AlgebraicClosure ℚ) jq = coeffMap A.subtype (jqModC ↥A) := by
    show (jqModC ℚ).map (algebraMap ℚ (AlgebraicClosure ℚ)) = (jqModC ↥A).map A.subtype
    rw [map_jqModC, map_jqModC]
  have hred : coeffMap (IsLocalRing.residue ↥A) (jqModC ↥A) = jqModC (ResidueField ↥A) := by
    show (jqModC ↥A).map _ = _
    exact map_jqModC _
  have hjκ0 : jqModC (ResidueField ↥A) ≠ 0 := fun h => by
    have h1 := ModularCurve.coeff_jqModC_neg_one (ResidueField ↥A)
    rw [h, HahnSeries.coeff_zero] at h1
    exact zero_ne_one h1
  have hjq0 : coeffEmb (AlgebraicClosure ℚ) jq ≠ 0 := by
    rw [← hcoej₁]
    exact fun h => hjt0 (Subtype.ext h)
  have hcoej' : ((j' : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) =
      coeffMap A.subtype (qExpand ↥A q (jqModC ↥A)) := by
    rw [hj', ModularCurve.coeffMap_qExpand, ← hjq]
    exact (ModularCurve.coeffMap_qExpand (algebraMap ℚ (AlgebraicClosure ℚ)) q jq)
  have hred' : coeffMap (IsLocalRing.residue ↥A) (qExpand ↥A q (jqModC ↥A)) ≠ 0 := by
    rw [ModularCurve.coeffMap_qExpand, hred]
    exact fun h => hjκ0 (qExpand_injective (R := ResidueField ↥A) (N := q) (by rw [h, map_zero]))
  have hj'0 : ((j' : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) ≠ 0 := by
    rw [hj']
    show coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) (qExpand ℚ q jq) ≠ 0
    rw [ModularCurve.coeffMap_qExpand]
    exact fun h => hjq0 (qExpand_injective (R := AlgebraicClosure ℚ) (N := q) (h.trans (map_zero _).symm))
  have h1ne : coeffMap (IsLocalRing.residue ↥A) 1 ≠ 0 := by rw [map_one]; exact one_ne_zero
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  ·
    refine (hO _).2 ⟨1, jqModC ↥A, by rw [hred]; exact hjκ0, ?_⟩
    rw [map_one, ← hjq]
    show ((j₁ : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ))⁻¹ * coeffEmb (AlgebraicClosure ℚ) jq = 1
    rw [hcoej₁, inv_mul_cancel₀ hjq0]
  ·
    refine (hO _).2 ⟨jqModC ↥A, 1, h1ne, ?_⟩
    rw [map_one, mul_one, hcoej₁, hjq]
  ·
    refine (hO _).2 ⟨1, qExpand ↥A q (jqModC ↥A), hred', ?_⟩
    rw [map_one, ← hcoej']
    show ((j' : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ))⁻¹ * _ = 1
    exact inv_mul_cancel₀ hj'0
  ·
    refine (hO _).2 ⟨qExpand ↥A q (jqModC ↥A), 1, h1ne, ?_⟩
    rw [map_one, mul_one, hcoej']
  ·
    intro a
    rw [halg a]
    have haA : ((a : ↥K₁) : AlgebraicClosure ℚ) ∈ A := (hA₁ (a : ↥K₁)).1 a.2
    refine (hO _).2 ⟨HahnSeries.single 0 ⟨_, haA⟩, 1, h1ne, ?_⟩
    rw [map_one, mul_one, coeffMap_single]
    show algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) ((a : ↥K₁) : AlgebraicClosure ℚ) = _
    rw [algebraMap_laurentSeries_eq_single]
    rfl

end TH1Wanted2
end FTW5
end P2MW.S_ModularCurve_FullLevel_exists_reads_resAut_smul_and_centred_iff_of_mem_closure_levelAutBar_twoChartIntegralModel_of_eq_three
