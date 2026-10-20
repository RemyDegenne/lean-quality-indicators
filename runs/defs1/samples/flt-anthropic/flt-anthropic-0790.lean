namespace P2MW.S_ModularCurve_FullLevel_Diamond_qExpand_mem_and_apply_eq_of_isLevelAutAt_of_mem_gamma0_of_eq_levelH_inf_ker

open scoped MatrixGroups ModularForm

open Matrix ModularCurve ModularCurve.FullLevel CongruenceSubgroup

open scoped Pointwise

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

noncomputable section

namespace FFH1

variable (m : ℕ) [NeZero m]

abbrev Dr : GL (Fin 2) ℝ := ModularForm.heckeDiagMatrix m

end FFH1
end
end P2MW.S_ModularCurve_FullLevel_Diamond_qExpand_mem_and_apply_eq_of_isLevelAutAt_of_mem_gamma0_of_eq_levelH_inf_ker
