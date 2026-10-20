namespace P2MW.S_ModularCurve_exists_ratCast_qExpansion_comp_smul_of_mem_Gamma0

set_option autoImplicit false

noncomputable section

open Complex UpperHalfPlane ModularForm CongruenceSubgroup Function

open scoped Real Manifold MatrixGroups ModularForm Topology

namespace X1DiamondRational

variable (N : ℕ)

section Group

variable (N : ℕ)

theorem T_mem_Gamma1 : ModularGroup.T ∈ Gamma1 N := by
  simpa using T_pow_mem_Gamma1 N 1

end Group
end X1DiamondRational
end
end P2MW.S_ModularCurve_exists_ratCast_qExpansion_comp_smul_of_mem_Gamma0
