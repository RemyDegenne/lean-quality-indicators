namespace P2MW.S_ModularCurve_FullLevel_AuxLevel_apply_eq_of_isLevelAutAt_of_coeffMap_mul_qExpansion_slash_eq

open scoped MatrixGroups

open Matrix ModularCurve ModularCurve.FullLevel CongruenceSubgroup

open scoped Pointwise

set_option autoImplicit false

set_option linter.unusedSectionVars false

p2m_reactivate

open scoped MatrixGroups ModularForm Manifold

open Matrix ModularCurve ModularCurve.FullLevel CongruenceSubgroup UpperHalfPlane HahnSeries

open scoped Pointwise

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

noncomputable section

namespace R4GC

section Group

variable (m : ℕ) [NeZero m]

variable {m}

def downMat (ε : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ := !![ε 0 0, ε 0 1 / m; (m : ℤ) * ε 1 0, ε 1 1]

end Group
end R4GC
end
end P2MW.S_ModularCurve_FullLevel_AuxLevel_apply_eq_of_isLevelAutAt_of_coeffMap_mul_qExpansion_slash_eq
