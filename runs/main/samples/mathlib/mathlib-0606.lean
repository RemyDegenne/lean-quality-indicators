@[expose] public section

namespace Pell

open Nat

section

variable {a : ℕ} (a1 : 1 < a)

theorem yn_modEq_a_sub_one : ∀ n, yn a1 n ≡ n [MOD a - 1]
  | 0 => by simp [Nat.ModEq.refl]
  | 1 => by simp [Nat.ModEq.refl]
  | n + 2 =>
    (yn_modEq_a_sub_one n).add_right_cancel <| by
      rw [yn_succ_succ, (by ring : n + 2 + n = 2 * (n + 1))]
      exact ((modEq_sub a1.le).mul_left 2).mul (yn_modEq_a_sub_one (n + 1))

end
end Pell
end
