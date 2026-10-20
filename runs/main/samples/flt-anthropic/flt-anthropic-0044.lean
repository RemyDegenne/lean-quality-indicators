namespace P2MW.S_ModularCurve_two_mul_genusFF_add_card_fibres_le_finrank_add_two_of_gamma1_le

attribute [-instance] AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion

set_option linter.unusedSectionVars false

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 1600000

set_option maxHeartbeats 3200000

noncomputable section

open scoped MatrixGroups

p2m_open

namespace ModularCurve

namespace RiemannHurwitzCount

p2m_open

universe u v

section Generic

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem not_ord_sub_pos_of_ord_sub_pos (v : Place K F) {x : F} {c c' : K} (hcc' : c ≠ c')
    (h : 0 < v.ord (x - algebraMap K F c)) : ¬ 0 < v.ord (x - algebraMap K F c') := by
  intro h'
  have hne : x - algebraMap K F c ≠ 0 := by rintro hh; rw [hh] at h; simp at h
  have hne' : x - algebraMap K F c' ≠ 0 := by rintro hh; rw [hh] at h'; simp at h'
  have hd : algebraMap K F (c' - c) ≠ 0 := (map_ne_zero _).mpr (sub_ne_zero.mpr hcc'.symm)
  have hsum : (x - algebraMap K F c) + -(x - algebraMap K F c') = algebraMap K F (c' - c) := by
    rw [map_sub]; ring
  have key := v.min_ord_le_ord_add hne (neg_ne_zero.mpr hne') (by rw [hsum]; exact hd)
  rw [hsum, v.ord_algebraMap] at key
  have : v.ord (-(x - algebraMap K F c')) = v.ord (x - algebraMap K F c') := by
    rw [show -(x - algebraMap K F c') = (x - algebraMap K F c') * (-1) by ring,
      v.ord_mul hne' (by norm_num), show (-1 : F) = algebraMap K F (-1) by simp,
      v.ord_algebraMap, add_zero]
  rw [this] at key
  have hmin : 0 < min (v.ord (x - algebraMap K F c)) (v.ord (x - algebraMap K F c')) := lt_min h h'
  omega

end Generic
end RiemannHurwitzCount
end ModularCurve
end
end P2MW.S_ModularCurve_two_mul_genusFF_add_card_fibres_le_finrank_add_two_of_gamma1_le
