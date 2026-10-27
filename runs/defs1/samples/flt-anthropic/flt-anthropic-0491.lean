namespace P2MW.S_ModularCurve_SiegelUnit_exists_modularForm_gamma1_isIntegralQExp_coeff_eq_one_and_forall_slash_isIntegral

set_option autoImplicit false

noncomputable section

open Complex UpperHalfPlane ModularForm CongruenceSubgroup Function

open scoped Real Manifold MatrixGroups ModularForm Topology Pointwise

namespace ModularCurve

namespace SiegelUnit

namespace WF1A

p2m_open

local notation "Γ₁(" M ")" => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

section Siegel

variable (N : ℕ)

def uProd [NeZero N] (m : ZMod N → ZMod N → ℕ) (τ : ℍ) : ℂ :=
  ∏ r : ZMod N, ∏ s : ZMod N, siegelFun N (r.val : ℤ) (s.val : ℤ) (τ : ℂ) ^ (12 * N * m r s)

end Siegel
end WF1A
end SiegelUnit
end ModularCurve
end
end P2MW.S_ModularCurve_SiegelUnit_exists_modularForm_gamma1_isIntegralQExp_coeff_eq_one_and_forall_slash_isIntegral
