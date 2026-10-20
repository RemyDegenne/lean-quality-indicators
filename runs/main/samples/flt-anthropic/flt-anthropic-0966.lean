namespace P2MW.S_ModularCurve_exists_place_of_emb

attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 1600000

set_option maxHeartbeats 6400000

noncomputable section

open ModularCurve AlgebraicCurve IntermediateField Polynomial

namespace S12P

variable (N : ℕ) [NeZero N]

theorem mem_iff_ord_nonneg (w : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N))
    {x : ↥(modularFunctionFieldBar N)} (hx : x ≠ 0) :
    x ∈ w.toValuationSubring ↔ 0 ≤ w.ord x := by
  rw [Place.mem_iff_adicValuation_le_one, Place.ord, neg_nonneg,
    WithZero.log_le_iff_le_exp (w.adicValuation_ne_zero hx), WithZero.exp_zero]

end S12P
end
end P2MW.S_ModularCurve_exists_place_of_emb
