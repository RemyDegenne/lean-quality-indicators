namespace P2MW.S_Matrix_exists_list_prod_elementary_eq_diagonal_of_det_map_mul_eq_one

set_option autoImplicit false

set_option linter.unusedSimpArgs false

set_option linter.unusedSectionVars false

namespace P2mWhitehead

open Matrix

section Ring

variable {A : Type*} [Ring A]

@[scoped simp] theorem E_true (t : A) : E (true, t) = !![(1 : A), t; 0, 1] := rfl

end Ring
end P2mWhitehead
end P2MW.S_Matrix_exists_list_prod_elementary_eq_diagonal_of_det_map_mul_eq_one
