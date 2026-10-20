namespace P2MW.S_ModularCurve_FullLevel_forall_isLevelAutAt_apply_eq_iff_exists_eq_qExpand

open scoped MatrixGroups ModularForm Manifold

open Matrix ModularCurve ModularCurve.FullLevel CongruenceSubgroup UpperHalfPlane HahnSeries

open scoped Pointwise

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

p2m_reactivate

open scoped MatrixGroups ModularForm

open Matrix ModularCurve ModularCurve.FullLevel CongruenceSubgroup

open scoped Pointwise

set_option autoImplicit false

set_option linter.unusedSectionVars false

noncomputable section

namespace W1xLE

variable (m : ℕ) [NeZero m]

@[scoped simp] theorem conjElemN_coe (γ : SL(2, ℤ)) : ((conjElemN m γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
    !![((γ 0 0 : ℤ) : ℝ), ((γ 0 1 : ℤ) : ℝ) / m; (m : ℝ) * ((γ 1 0 : ℤ) : ℝ), ((γ 1 1 : ℤ) : ℝ)] := rfl

end W1xLE
end
end P2MW.S_ModularCurve_FullLevel_forall_isLevelAutAt_apply_eq_iff_exists_eq_qExpand
