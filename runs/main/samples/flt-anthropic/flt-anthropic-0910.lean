namespace P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_modularForm_weight_four_qExpansion_eq_c4

open scoped MatrixGroups

open Matrix ModularCurve ModularCurve.FullLevel CongruenceSubgroup

open scoped Pointwise

set_option autoImplicit false

set_option linter.unusedSectionVars false

noncomputable section

namespace W1xLA

variable (m : ℕ) [NeZero m]

theorem conjElemN_mul (γ δ : SL(2, ℤ)) : conjElemN m (γ * δ) = conjElemN m γ * conjElemN m δ := by
  simp only [conjElemN_eq, map_mul]; group

end W1xLA
end
end P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_modularForm_weight_four_qExpansion_eq_c4
