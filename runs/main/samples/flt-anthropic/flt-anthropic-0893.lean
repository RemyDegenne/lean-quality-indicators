namespace P2MW.S_ModularCurve_IsInfReductionMap_smul_diffQExp_pullbackAlong_eq_ofPowerSeries_map_of_reduction_slash_fricke

attribute [-instance] AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.PhiGen.instNeZeroPhiGenCosetA

set_option autoImplicit false

set_option maxHeartbeats 6400000

set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open scoped MatrixGroups ModularForm Pointwise TensorProduct

open UpperHalfPlane HahnSeries CongruenceSubgroup CohCarrier

namespace FrickeReadB

section SpecB

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M} [NeZero (M / p)]
  {K : Type*} [Field K] {φ : ↥(integralClosure ℤ ℂ) →+* K} {WQ : GL (Fin 2) ℝ}

theorem weight_eq (w : ℕ) :
    ((4 : ℕ) : ℤ) + ((4 : ℕ) : ℤ) + ((6 : ℕ) : ℤ) + (w : ℤ) = ((2 : ℤ) + w) + 12 := by push_cast; ring

end SpecB
end FrickeReadB
end
end P2MW.S_ModularCurve_IsInfReductionMap_smul_diffQExp_pullbackAlong_eq_ofPowerSeries_map_of_reduction_slash_fricke
