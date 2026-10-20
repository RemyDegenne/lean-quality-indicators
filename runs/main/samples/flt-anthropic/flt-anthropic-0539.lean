namespace P2MW.S_ModularCurve_SiegelUnit_qExpansion_one_coeff_of_coe_eq_prod_siegelFun_pow_mul_discriminant_pow

set_option autoImplicit false

noncomputable section

namespace INTINF

open Complex UpperHalfPlane PowerSeries Filter Topology

local notation "𝕢" => Function.Periodic.qParam

theorem CoeffMem.pow {A : Subalgebra ℤ ℂ} {S : PowerSeries ℂ} (hS : CoeffMem A S) :
    ∀ n : ℕ, CoeffMem A (S ^ n)
  | 0 => by simpa using CoeffMem_X_pow A 0
  | n + 1 => by
    rw [pow_succ]
    exact (CoeffMem.pow hS n).mul hS

end INTINF
end
end P2MW.S_ModularCurve_SiegelUnit_qExpansion_one_coeff_of_coe_eq_prod_siegelFun_pow_mul_discriminant_pow
