namespace P2MW.S_ModularCurve_mem_regularDifferentials_x1FunctionFieldBar_of_coeffMap_diffQExp_eq_qExpansion

attribute [-instance] AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA

open UpperHalfPlane ModularCurve AlgebraicCurve

open scoped MatrixGroups

namespace SolB8bd4cf51

theorem coeffMap_coeffEmb' {L₁ L₂ : Type*} [Field L₁] [Field L₂] [Algebra ℚ L₁] [Algebra ℚ L₂]
    (σ : L₁ →+* L₂) (x : LaurentSeries ℚ) :
    coeffMap σ (coeffEmb L₁ x) = coeffEmb L₂ x := by
  rw [coeffEmb, coeffEmb, coeffMap_coeffMap,
    Subsingleton.elim (σ.comp (algebraMap ℚ L₁)) (algebraMap ℚ L₂)]

end SolB8bd4cf51
end P2MW.S_ModularCurve_mem_regularDifferentials_x1FunctionFieldBar_of_coeffMap_diffQExp_eq_qExpansion
