@[expose] public section

open Finset

namespace Polynomial

universe u v

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

section Semiring

variable [Semiring R] {p q r : R[X]}

@[simp, grind =]
theorem natDegree_C (a : R) : natDegree (C a) = 0 := by
  by_cases ha : a = 0
  · have : C a = 0 := by rw [ha, C_0]
    rw [natDegree, degree_eq_bot.2 this, WithBot.unbotD_bot]
  · rw [natDegree, degree_C ha, WithBot.unbotD_zero]

end Semiring
end Polynomial
end
