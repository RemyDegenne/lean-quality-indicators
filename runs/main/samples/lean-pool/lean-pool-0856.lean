@[expose] public section

open Filter Asymptotics

variable (R : RamanujanTau)

namespace E2Helpers

namespace E2XBoundHelpers

lemma B_pos_of_x11_lt_y2 (x : ℕ+) (y : ℤ)
    (hlt : (↑(x : ℕ) : ℤ) ^ 11 < y ^ 2) :
    0 < y.natAbs ^ 2 - (x : ℕ) ^ 11 := by
  apply Nat.sub_pos_of_lt
  rw [← Int.natAbs_sq y] at hlt
  exact_mod_cast hlt

end E2XBoundHelpers
end E2Helpers
end
