namespace P2MW.S_ModularCurve_exists_ratCast_qExpansion_comp_smul_of_mem_Gamma0_of_dvd

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

noncomputable section

open Complex UpperHalfPlane ModularForm CongruenceSubgroup Function

open scoped Real Manifold MatrixGroups ModularForm Topology

namespace A2ALRat

variable (N : ℕ)

def kN : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ {zetaN N}

end A2ALRat
end
end P2MW.S_ModularCurve_exists_ratCast_qExpansion_comp_smul_of_mem_Gamma0_of_dvd
