namespace P2MW.S_ModularCurve_FullLevel_exists_isLevelAutAt_conj_of_isLevelAutAt_of_isPrimitiveRoot

open scoped MatrixGroups

open Matrix ModularCurve ModularCurve.FullLevel CongruenceSubgroup

open scoped Pointwise

set_option autoImplicit false

set_option linter.unusedSectionVars false

noncomputable section

namespace W1TW

variable (m : ℕ) [NeZero m]

theorem mneZ : (m : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne m

end W1TW
end
end P2MW.S_ModularCurve_FullLevel_exists_isLevelAutAt_conj_of_isLevelAutAt_of_isPrimitiveRoot
