namespace P2MW.S_ModularCurve_valuation_lt_one_of_ord_sub_pos_of_coeff_lt_one

attribute [-instance] AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion

set_option autoImplicit false

noncomputable section

namespace ValLtOneS8da

p2m_open

variable (N : ℕ) [NeZero N]

variable (A : ValuationSubring (AlgebraicClosure ℚ))

variable {k : Type*} [Field k] (red : A →+* k)

abbrev O : Subring (LaurentSeries (AlgebraicClosure ℚ)) :=
  modularLocalized N A.toSubring (redS A red)

end ValLtOneS8da
end
end P2MW.S_ModularCurve_valuation_lt_one_of_ord_sub_pos_of_coeff_lt_one
