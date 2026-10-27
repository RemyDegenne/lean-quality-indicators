namespace P2MW.S_ModularCurve_DRModel_exists_curveModel_closedImmersion_pair_pFibre_cover_levelSet_singleton

attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option autoImplicit false

universe u

p2m_open

open scoped TensorProduct

noncomputable section

namespace GLUECI

open AlgebraicCurve.TwoChartIntegralModel

section Schemes

variable {R : Type u} [CommRing R] {F : Type u} [Field F] [Algebra R F] {j : F} [Fact (j ≠ 0)]
  {κ : Type u} [Field κ] [Algebra R κ] {L : Type u} [Field L] [Algebra κ L] {t : L} [Fact (t ≠ 0)]
  (D : GlueDatum R F j κ t)

abbrev PInf (_D : GlueDatum R F j κ t) :=
  pullback (TwoChartIntegralModel.ιInf R F j) (pullback.fst (toBase R F j) (baseMap R κ))

end Schemes
end GLUECI
end
end P2MW.S_ModularCurve_DRModel_exists_curveModel_closedImmersion_pair_pFibre_cover_levelSet_singleton
