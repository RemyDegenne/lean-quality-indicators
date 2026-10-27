public section

namespace CFSG.PSL2Table

open Matrix

open scoped MatrixGroups

open CFSG CFSG.BrauerThirdMainTheorem.Helpers

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

section ThreeModEight

omit [DecidableEq F] in
theorem card_PSL_of_eq_three (hF : ringChar F ≠ 2) {k : ℕ} (hk : Fintype.card F = 8 * k + 3) :
    (Nat.card PSL(2, F) : ℂ) = 4 * (8 * k + 3) * (8 * k ^ 2 + 6 * k + 1) := by
  rw [card_PSL_complex hF, hk]
  push_cast
  ring

end ThreeModEight
end CFSG.PSL2Table
end
