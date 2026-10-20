namespace P2MW.S_ModularCurve_DRModel_exists_chartAlgInf_mul_sub_one_mem_nonunits_of_valuationSubring_pair

attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA

set_option autoImplicit false

set_option maxHeartbeats 800000

set_option synthInstance.maxHeartbeats 400000

set_option Elab.async false

open scoped Polynomial

noncomputable section

open AlgebraicCurve

namespace TensorAdapt

section MidLift

open AlgebraicCurve.TwoChartIntegralModel

variable (p : ℕ) [Fact p.Prime] {F : Type} [Field F] (j : F) [Fact (j ≠ 0)]
  (𝔭 : Ideal ↥(chartAlgFin ℤ F j)) (e : (↥(chartAlgFin ℤ F j) ⧸ 𝔭) ≃+* (ZMod p)[X]) (m : ℕ)

theorem ρ₀_apply (b : ↥(chartAlgFin ℤ F j)) :
    ρ₀ p j 𝔭 e b = Polynomial.aeval (RatFunc.X : RatFunc (ZMod p)) (e (Ideal.Quotient.mk 𝔭 b)) := rfl

end MidLift
end TensorAdapt
end
end P2MW.S_ModularCurve_DRModel_exists_chartAlgInf_mul_sub_one_mem_nonunits_of_valuationSubring_pair
