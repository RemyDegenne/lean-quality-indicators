namespace P2MW.S_Ihara_mennickeZ_eq_top_of_corrected_reading_of_diophantine

set_option Elab.async false

set_option autoImplicit false

set_option autoImplicit false

namespace Ihara

p2m_open

open Subgroup Matrix

open scoped MatrixGroups

noncomputable section

variable (q : ℕ)

theorem qInv_pow_mul_mul_qInv_pow (k : ℕ) (x : ZAway q) :
    qInv q ^ k * x * qInv q ^ k = x * qInv q ^ (2 * k) := by
  rw [two_mul, pow_add]; ring

end
end Ihara
end P2MW.S_Ihara_mennickeZ_eq_top_of_corrected_reading_of_diophantine
