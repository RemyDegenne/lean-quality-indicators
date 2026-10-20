@[expose] public section

open Equiv Equiv.Perm Finset

variable {n m R : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommSemiring R]

variable (s : ℤˣ) (A B : Matrix n n R) (i j : n)

namespace Matrix

variable {A} {a b c : R}

lemma IsDetpBalanced.mul_add_mul_eq (h : A.IsDetpBalanced a b) (s t : ℤˣ) :
    a * A.detp s + b * A.detp t = b * A.detp s + a * A.detp t := by
  obtain rfl | rfl := Int.units_eq_one_or s <;> obtain rfl | rfl := Int.units_eq_one_or t
  · rw [add_comm]
  · rw [h]
  · rw [add_comm, ← h, add_comm]
  · rw [add_comm]

end Matrix
end
