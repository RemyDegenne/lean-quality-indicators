namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_den_circleDeg_eq_one_and_den_depthMoment_eq_one_of_inertiaStable

attribute [-instance] AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA

set_option synthInstance.maxHeartbeats 1600000

set_option maxHeartbeats 3200000

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

namespace S12EL

namespace Int

theorem den_eq_one_of_eq_intCast {x : ℚ} {m : ℤ} (h : x = m) : x.den = 1 := by
  rw [h]; exact Rat.den_intCast m

end Int
end S12EL
end P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_den_circleDeg_eq_one_and_den_depthMoment_eq_one_of_inertiaStable
