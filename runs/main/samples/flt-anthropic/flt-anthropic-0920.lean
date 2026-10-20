namespace P2MW.S_ModularCurve_PlaceSpecialization_jFun_add_C_mul_jqFun_sub_algebraMap_ne_zero

attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 1600000

set_option maxHeartbeats 3200000

p2m_open

namespace ModularCurve

namespace PlaceSpecialization

p2m_open

section PencilLine

variable {q : ℕ} [Fact q.Prime]

theorem ord_cuspZeroBar_eq (f : modularFunctionFieldBar (1 * q)) :
    (cuspZeroBar (1 * q)).ord f = (cuspInftyBar (1 * q)).ord (frickeInvolutionBar (1 * q) f) := by
  conv_lhs => rw [← ModularCurve.frickeInvolutionBar_frickeInvolutionBar (1 * q) f]
  exact Place.ord_smul (frickeInvolutionBar (1 * q)) (cuspInftyBar (1 * q)) (frickeInvolutionBar (1 * q) f)

end PencilLine
end PlaceSpecialization
end ModularCurve
end P2MW.S_ModularCurve_PlaceSpecialization_jFun_add_C_mul_jqFun_sub_algebraMap_ne_zero
