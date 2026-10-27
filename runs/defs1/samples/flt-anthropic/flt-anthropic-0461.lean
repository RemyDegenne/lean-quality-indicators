namespace P2MW.S_ModularCurve_jIntegralClosure_isNoetherianRing_and_isIntegrallyClosed_level

attribute [-instance] AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 1600000

set_option maxHeartbeats 6400000

p2m_open

namespace ModularCurve

p2m_open

namespace NodeLocalized

p2m_open

noncomputable section

variable (A : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
  (N : ℕ) [NeZero N]

@[reducible] def jRingModularRangeAlgebra : Algebra ↥(jRing A K) ↥(modularRange N (coeffSubring A K)) :=
  (Subring.inclusion (jRing_le_modularRange A K N)).toAlgebra

end
end NodeLocalized
end ModularCurve
end P2MW.S_ModularCurve_jIntegralClosure_isNoetherianRing_and_isIntegrallyClosed_level
