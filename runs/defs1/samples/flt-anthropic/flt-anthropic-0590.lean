namespace P2MW.S_ModularCurve_qExpansion_coeff_comp_smul_mem_adjoin_exp_of_gamma1_mul

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

noncomputable section

open Complex UpperHalfPlane ModularForm CongruenceSubgroup Function

open scoped Real Manifold MatrixGroups ModularForm Topology

namespace ALRatFun

variable (N : ℕ)

abbrev Idx : Type := Option {v : Fin 2 → ZMod N // v ≠ 0}

end ALRatFun
end
end P2MW.S_ModularCurve_qExpansion_coeff_comp_smul_mem_adjoin_exp_of_gamma1_mul
