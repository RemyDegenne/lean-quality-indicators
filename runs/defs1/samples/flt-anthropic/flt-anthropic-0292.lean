namespace P2MW.S_ModularCurve_FullLevel_Diamond_mem_and_apply_eq_of_isLevelAutAt_of_mem_Gamma_of_eq_levelH_inf_ker

set_option autoImplicit false

open scoped MatrixGroups

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

noncomputable section

open scoped MatrixGroups ModularForm

open Matrix ModularCurve ModularCurve.FullLevel CongruenceSubgroup

namespace FGH1

section Emb

open UpperHalfPlane HahnSeries

variable {L : Type} [Field L] [CharZero L]

variable (ι₀ : L →+* ℂ)

abbrev ιB : LaurentSeries L →+* LaurentSeries ℂ := coeffMap ι₀

end Emb
end FGH1
end
end P2MW.S_ModularCurve_FullLevel_Diamond_mem_and_apply_eq_of_isLevelAutAt_of_mem_Gamma_of_eq_levelH_inf_ker
