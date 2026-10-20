namespace P2MW.S_ModularCurve_isIntegralElem_div_delta_pow_and_div_eisenstein4_pow_of_forall_qExpansion_slash_isIntegral

set_option autoImplicit false

set_option linter.unusedSectionVars false

noncomputable section

open scoped MatrixGroups ModularForm

namespace ChartMemNorm

open ModularForm UpperHalfPlane SlashInvariantForm Polynomial

variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] {k : ℤ}

abbrev Cos (Γ : Subgroup SL(2, ℤ)) : Type := ↥𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ

end ChartMemNorm
end
end P2MW.S_ModularCurve_isIntegralElem_div_delta_pow_and_div_eisenstein4_pow_of_forall_qExpansion_slash_isIntegral
