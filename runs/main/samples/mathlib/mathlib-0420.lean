@[expose] public section

noncomputable section

@[inherit_doc] scoped[Polynomial] notation:9000 R "[X]" => Polynomial R

open AddMonoidAlgebra Finset Module

open Finsupp hiding single

open Function hiding Commute

namespace Polynomial

universe u

variable {R : Type u} {a b : R} {m n : ℕ}

section Semiring

variable [Semiring R] {p q : R[X]}

@[simp]
theorem support_X_pow [Nontrivial R] (n : ℕ) : (X ^ n : R[X]).support = singleton n := by
  convert support_monomial n (NeZero.out (n := (1 : R)))
  exact X_pow_eq_monomial n

end Semiring
end Polynomial
end
end
