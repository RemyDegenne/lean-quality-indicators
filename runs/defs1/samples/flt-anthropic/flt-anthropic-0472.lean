namespace P2MW.S_AlgebraicCurve_Divisor_isPrincipal_of_forall_isPrincipal_mapDomain_placeReduction

attribute [-instance] AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal

attribute [-instance] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion

p2m_open

namespace AlgebraicCurve

namespace SpecializationPrincipleAux

p2m_open

open IsLocalRing

universe uK uF uE uFE

section Reduction

variable {E : Type uE} {FE : Type uFE} [Field E] [Field FE] [Algebra E FE]

variable (A : ValuationSubring E)

def compositeRing [IsAlgClosed E] (P : Place E FE) [Module.Finite E P.ResidueField] :
    ValuationSubring FE where
  carrier := {g | ∃ a : E, a ∈ A ∧ P.toValuationSubring.valuation (g - algebraMap E FE a) < 1}
  mul_mem' := by
    rintro g h ⟨a, haA, ha⟩ ⟨b, hbA, hb⟩
    refine ⟨a * b, mul_mem haA hbA, ?_⟩
    have hg1 : P.toValuationSubring.valuation g ≤ 1 :=
      (P.toValuationSubring.valuation_le_one_iff _).2 (mem_of_valuation_sub_lt_one P ha)
    have : g * h - algebraMap E FE (a * b) =
        g * (h - algebraMap E FE b) + algebraMap E FE b * (g - algebraMap E FE a) := by
      rw [map_mul]; ring
    rw [this]
    refine Valuation.map_add_lt _ ?_ ?_
    · rw [map_mul]
      calc P.toValuationSubring.valuation g * P.toValuationSubring.valuation (h - algebraMap E FE b)
          ≤ 1 * P.toValuationSubring.valuation (h - algebraMap E FE b) :=
            mul_le_mul_left hg1 _
        _ < 1 := by rw [one_mul]; exact hb
    · rw [map_mul]
      calc P.toValuationSubring.valuation (algebraMap E FE b) *
            P.toValuationSubring.valuation (g - algebraMap E FE a)
          ≤ 1 * P.toValuationSubring.valuation (g - algebraMap E FE a) :=
            mul_le_mul_left (valuation_algebraMap_le_one P b) _
        _ < 1 := by rw [one_mul]; exact ha
  one_mem' := ⟨1, one_mem A, by simp⟩
  add_mem' := by
    rintro g h ⟨a, haA, ha⟩ ⟨b, hbA, hb⟩
    refine ⟨a + b, add_mem haA hbA, ?_⟩
    have : g + h - algebraMap E FE (a + b) = (g - algebraMap E FE a) + (h - algebraMap E FE b) := by
      rw [map_add]; ring
    rw [this]
    exact Valuation.map_add_lt _ ha hb
  zero_mem' := ⟨0, zero_mem A, by simp⟩
  neg_mem' := by
    rintro g ⟨a, haA, ha⟩
    refine ⟨-a, neg_mem haA, ?_⟩
    have : -g - algebraMap E FE (-a) = -(g - algebraMap E FE a) := by rw [map_neg]; ring
    rw [this, Valuation.map_neg]
    exact ha
  mem_or_inv_mem' := by
    intro g
    simp only [Set.mem_setOf_eq]
    by_cases hg : g ∈ P.toValuationSubring
    · obtain ⟨e, he⟩ := exists_valuation_sub_lt_one P hg
      by_cases heA : e ∈ A
      · exact Or.inl ⟨e, heA, he⟩
      · right
        have he0 : e ≠ 0 := by rintro rfl; exact heA (zero_mem A)
        have heinv : e⁻¹ ∈ A := (A.mem_or_inv_mem e).resolve_left heA
        exact ⟨e⁻¹, heinv, valuation_inv_sub_inv_lt_one P he0 he⟩
    ·
      right
      refine ⟨0, zero_mem A, ?_⟩
      have hg' : g⁻¹ ∈ P.toValuationSubring := (P.toValuationSubring.mem_or_inv_mem g).resolve_left hg
      have hg0 : g ≠ 0 := by rintro rfl; exact hg (zero_mem _)
      rcases P.toValuationSubring.valuation_lt_one_or_eq_one ⟨g⁻¹, hg'⟩ with hlt | heq
      · simpa using hlt
      · exfalso
        apply hg
        rw [← ValuationSubring.valuation_le_one_iff]
        have : P.toValuationSubring.valuation g⁻¹ = 1 := heq
        rw [Valuation.map_inv, inv_eq_one] at this
        exact this.le

end Reduction
end SpecializationPrincipleAux
end AlgebraicCurve
end P2MW.S_AlgebraicCurve_Divisor_isPrincipal_of_forall_isPrincipal_mapDomain_placeReduction
