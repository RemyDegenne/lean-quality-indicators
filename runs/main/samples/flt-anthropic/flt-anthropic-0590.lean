namespace P2MW.S_CohCarrier_heckeT_heckeT_eq_self_of_jDeg_one_eq_zero_of_jDeg_eq_zero

set_option autoImplicit false

set_option linter.unusedSectionVars false

namespace ALInvolSol

open MulAction

section Concrete

open CohCarrier CongruenceSubgroup

open scoped MatrixGroups

variable {M q : ℕ} [NeZero M] [NeZero q]

section entries

variable (u v : ℤ) (huv : u * q + v * M = 1)

@[scoped simp] theorem wMat_01 : (wMat (M := M) (q := q) u v huv) 0 1 = -v := rfl

end entries
end Concrete
end ALInvolSol
end P2MW.S_CohCarrier_heckeT_heckeT_eq_self_of_jDeg_one_eq_zero_of_jDeg_eq_zero
