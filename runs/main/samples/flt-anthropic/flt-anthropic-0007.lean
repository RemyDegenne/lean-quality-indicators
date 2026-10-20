namespace P2MW.S_CuspForm_norm_lt_of_heckeTLin_eq_smul

set_option autoImplicit false

noncomputable section

open MeasureTheory UpperHalfPlane ModularForm Filter

open scoped MatrixGroups ModularForm ComplexConjugate Modular ENNReal Pointwise

namespace AlliAux1HB

section norms

theorem heckeDiagMatrix_one : heckeDiagMatrix 1 = 1 := by
  apply Units.ext; rw [val_heckeDiagMatrix one_ne_zero, Units.val_one]
  ext i j; fin_cases i <;> fin_cases j <;> simp

end norms
end AlliAux1HB
end
end P2MW.S_CuspForm_norm_lt_of_heckeTLin_eq_smul
