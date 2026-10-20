namespace P2MW.S_ModularCurve_genusFF_modularFunctionFieldFullC_eq_genusFF_modularFunctionFieldBar

attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.Gamma0Pair.isElliptic WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral

attribute [-instance] ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular

noncomputable section

p2m_reactivate

set_option synthInstance.maxHeartbeats 1600000

set_option maxHeartbeats 3200000

open AlgebraicCurve ModularCurve

namespace A1b2bGenusFF

p2m_reactivate

p2m_reactivate

section Glue

variable {k K : Type*} [Field k] [Field K] (φ : k →+* K) (N : ℕ) [NeZero N]

omit [NeZero N] in

theorem coeffMap_mem_fullC {x : LaurentSeries k} (hx : x ∈ modularFunctionFieldFullC k N) :
    coeffMap φ x ∈ modularFunctionFieldFullC K N := by
  change x ∈ IntermediateField.adjoin k (divisorExpansionsC k N) at hx
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx =>
    obtain ⟨d, hd, hdN, rfl⟩ := hx
    rw [ModularCurve.coeffMap_qExpand, coeffMap_jqModC]
    exact jqModCd_mem_full K N hdN
  | algebraMap c =>
    rw [coeffMap_algebraMap_const]
    exact IntermediateField.algebraMap_mem _ _
  | add x y _ _ hx hy =>
    rw [map_add]
    exact add_mem hx hy
  | inv x _ hx =>
    rw [map_inv₀]
    exact inv_mem hx
  | mul x y _ _ hx hy =>
    rw [map_mul]
    exact mul_mem hx hy

end Glue
end A1b2bGenusFF
end
end P2MW.S_ModularCurve_genusFF_modularFunctionFieldFullC_eq_genusFF_modularFunctionFieldBar
