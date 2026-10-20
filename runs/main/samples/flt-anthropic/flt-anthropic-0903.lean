namespace P2MW.S_ModularCurve_isIntegralElem_div_delta_pow_and_div_eisenstein4_pow_of_forall_qExpansion_slash_isIntegral

set_option autoImplicit false

set_option linter.unusedSectionVars false

noncomputable section

open scoped MatrixGroups ModularForm

p2m_reactivate

p2m_reactivate

p2m_reactivate

namespace ChartMemAsm

open ModularForm UpperHalfPlane ModularCurve Polynomial CongruenceSubgroup SlashInvariantForm ChartMemNorm HahnSeries

p2m_reactivate

section IntegralUpToM

variable (M : ℕ) [NeZero M]

theorem mem_Tint_of_qExpand_mem {x : LaurentSeries ℂ} (h : qExpand ℂ M x ∈ Tint M) : x ∈ Tint M := fun n => by
  rw [coeff_eq_qExpand_coeff ℂ M x n]; exact h _

end IntegralUpToM
end ChartMemAsm
end
end P2MW.S_ModularCurve_isIntegralElem_div_delta_pow_and_div_eisenstein4_pow_of_forall_qExpansion_slash_isIntegral
