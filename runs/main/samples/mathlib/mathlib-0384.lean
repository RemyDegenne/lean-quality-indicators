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

theorem support_add : (p + q).support ⊆ p.support ∪ q.support := by
  simpa [support] using! Finsupp.support_add

end Semiring
end Polynomial
end
end
