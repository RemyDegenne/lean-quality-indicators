namespace P2MW.S_ModularCurve_exists_sum_smul_coeffEmb_of_mem_integers_of_cuspRegular

attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 1600000

set_option maxHeartbeats 3200000

noncomputable section

open AlgebraicCurve ModularCurve IsLocalRing

namespace CuspRegComb

section RatDVR

variable (A : ValuationSubring (AlgebraicClosure ℚ)) (q : ℕ) [hq : Fact q.Prime]

abbrev ratPart : ValuationSubring ℚ := A.comap (algebraMap ℚ (AlgebraicClosure ℚ))

end RatDVR
end CuspRegComb
end
end P2MW.S_ModularCurve_exists_sum_smul_coeffEmb_of_mem_integers_of_cuspRegular
