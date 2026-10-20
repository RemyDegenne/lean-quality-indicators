@[expose] public section

noncomputable section

open Finsupp Finset

open Polynomial

namespace Polynomial

universe u v

variable {R : Type u} {S : Type v} {a b c : R} {n m : ℕ}

section Semiring

variable [Semiring R] {p q : R[X]}

theorem leadingCoeff_add_of_degree_eq (h : degree p = degree q)
    (hlc : leadingCoeff p + leadingCoeff q ≠ 0) :
    leadingCoeff (p + q) = leadingCoeff p + leadingCoeff q := by
  have : natDegree (p + q) = natDegree p := by
    apply natDegree_eq_of_degree_eq
    rw [degree_add_eq_of_leadingCoeff_add_ne_zero hlc, h, max_self]
  simp only [leadingCoeff, this, natDegree_eq_of_degree_eq h, coeff_add]

end Semiring
end Polynomial
end
end
