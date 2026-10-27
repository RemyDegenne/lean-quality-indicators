namespace P2MW.S_ModularCurve_FullLevel_Diamond_mem_and_apply_eq_of_isLevelAutAt_of_mem_Gamma_of_eq_levelH_inf_ker

set_option autoImplicit false

open scoped MatrixGroups

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

noncomputable section

open scoped MatrixGroups ModularForm

open Matrix ModularCurve ModularCurve.FullLevel CongruenceSubgroup

namespace FGH1

section Dn

variable (m : ℕ) [NeZero m]

def dnMat (δ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ := !![δ 0 0, δ 0 1 / m; (m : ℤ) * δ 1 0, δ 1 1]

end Dn
end FGH1
end
end P2MW.S_ModularCurve_FullLevel_Diamond_mem_and_apply_eq_of_isLevelAutAt_of_mem_Gamma_of_eq_levelH_inf_ker
