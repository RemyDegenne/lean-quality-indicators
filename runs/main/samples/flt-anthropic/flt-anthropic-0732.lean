namespace P2MW.S_DrinfeldCurve_natCard_place_restrictAlong_eq_hFunctionFieldAction_smul

attribute [-instance] instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion

set_option autoImplicit false

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

namespace DrinfeldCurve

p2m_open

namespace GenCount

open AlgebraicCurve DrinfeldCurve.CNTAux Polynomial

open scoped Classical Pointwise

set_option linter.unusedSectionVars false

section InftyRel

variable (q : ℕ) [hq : Fact q.Prime] (k : Type) [Field k] [Algebra (GaloisField q 2) k] [IsAlgClosed k]
  [IsDomain (CoordRing q k)]
  (φ : drinfeldFunctionField q k →ₐ[k] drinfeldFunctionField q k) (hφi : φ.toRingHom.IsIntegral)
  (hφx : φ (CNTAux.xF q k) = CNTAux.xF q k ^ q ^ 2) (hφy : φ (CNTAux.yF q k) = CNTAux.yF q k ^ q ^ 2)
  (p : hSubgroup q)

theorem hmx_apply : hmx q p 0 0 = ((gm q p).det)⁻¹ * gm q p 1 1 ∧ hmx q p 0 1 = -(((gm q p).det)⁻¹ * gm q p 0 1) ∧
    hmx q p 1 0 = -(((gm q p).det)⁻¹ * gm q p 1 0) ∧ hmx q p 1 1 = ((gm q p).det)⁻¹ * gm q p 0 0 := by
  have hD := det_gm_ne_zero q p
  rw [hmx_eq, Matrix.inv_def, Matrix.adjugate_fin_two, Ring.inverse_eq_inv']
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [Matrix.smul_apply] <;> ring

end InftyRel
end GenCount
end DrinfeldCurve
end P2MW.S_DrinfeldCurve_natCard_place_restrictAlong_eq_hFunctionFieldAction_smul
