namespace P2MW.S_ModularCurve_exists_forall_coeff_smul_mem_of_forall_ord_neg

attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt

set_option synthInstance.maxHeartbeats 1600000

set_option maxHeartbeats 3200000

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

set_option linter.unusedSimpArgs false

noncomputable section

open ModularCurve HahnSeries PowerSeries

p2m_reactivate

p2m_reactivate

p2m_reactivate

noncomputable section

open PowerSeries Polynomial Filter Topology

p2m_reactivate

p2m_reactivate

noncomputable section

open PowerSeries

p2m_reactivate

namespace CuspDisc

section PlaceArg

open AlgebraicCurve ModularCurve MvPolynomial

variable (N : ℕ) [NeZero N]

local notation "ℚbar" => AlgebraicClosure ℚ

local notation "FN" => modularFunctionFieldBar N

variable (K : IntermediateField ℚ ℚbar)

def evQ : MvPolynomial (GenIdx N) K →+* LaurentSeries ℚbar :=
  (HahnSeries.ofPowerSeries ℤ ℚbar).comp
    ((MvPolynomial.aeval (genPS ℚbar N)).toRingHom.comp (MvPolynomial.map (algebraMap K ℚbar)))

end PlaceArg
end CuspDisc
end
end
end
end P2MW.S_ModularCurve_exists_forall_coeff_smul_mem_of_forall_ord_neg
