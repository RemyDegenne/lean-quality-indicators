public section

open scoped BigOperators Classical

namespace CFSG.Walter.Ward

open CFSG

namespace PSLData

variable {L : Type} [Group L] [Fintype L] {q : ℕ} {e : ℤ} (D : PSLData L q e)

theorem orderOf_sq_s₀ : orderOf ((D.s₀ : L) ^ 2) = D.m := by
  rw [orderOf_pow' _ two_ne_zero, D.orderOf_s₀, D.card_E_eq, Nat.gcd_mul_right_left]
  · simp

end PSLData
end CFSG.Walter.Ward
end
