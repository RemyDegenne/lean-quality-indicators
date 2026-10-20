namespace P2MW.S_ModularCurve_DRModel_exists_curveModel_closedImmersion_pair_pFibre_cover_levelSet_singleton

attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option autoImplicit false

universe u

p2m_open

open scoped TensorProduct

p2m_reactivate

set_option synthInstance.maxHeartbeats 400000

set_option Elab.async false

noncomputable section

p2m_open

open scoped TensorProduct

p2m_reactivate

p2m_open_scoped

p2m_reactivate

p2m_open_scoped

p2m_reactivate

p2m_open

p2m_open_scoped

noncomputable section

p2m_reactivate

p2m_reactivate

namespace GLUECI

open AlgebraicCurve.TwoChartIntegralModel

p2m_reactivate

section LevelSets

variable {R : Type u} [CommRing R] {F : Type u} [Field F] [Algebra R F] {j : F} [Fact (j ≠ 0)]
  {κ : Type u} [Field κ] [Algebra R κ] {L : Type u} [Field L] [Algebra κ L] {t : L} [Fact (t ≠ 0)]

variable (D : GlueDatum R F j κ t) (ht : Transcendental κ t)
  (hchart : ∀ x : L, x ∈ chartRing κ ({t} : Set L) ↔ ∃ f : κ[X], Polynomial.aeval t f = x)
  (hchartInv : ∀ x : L, x ∈ chartRing κ ({t⁻¹} : Set L) ↔ ∃ f : κ[X], Polynomial.aeval t⁻¹ f = x)

omit [Fact (t ≠ 0)] in
include ht hchartInv in

theorem eq_span_tInvChart_of_mem (𝔮 : Ideal ↥(chartRing κ ({t⁻¹} : Set L))) [𝔮.IsPrime]
    (h : tInvChart κ t ∈ 𝔮) : 𝔮 = Ideal.span {tInvChart κ t} := by
  have h' := eq_span_of_pow_mem κ t⁻¹ (transcendental_inv κ t ht) hchartInv (m := 1) 0 𝔮
    (by rwa [map_zero, sub_zero, pow_one])
  rwa [map_zero, sub_zero] at h'

end LevelSets
end GLUECI
end
end
end P2MW.S_ModularCurve_DRModel_exists_curveModel_closedImmersion_pair_pFibre_cover_levelSet_singleton
