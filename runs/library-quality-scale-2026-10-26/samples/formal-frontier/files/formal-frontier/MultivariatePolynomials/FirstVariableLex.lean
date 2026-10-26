/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.RingTheory.MvPolynomial.MonomialOrder

@[expose] public section

/-!
# First-variable lexicographic degree

A nonzero scalar top coefficient after `MvPolynomial.finSuccEquiv` fixes the
maximum lexicographic exponent of a multivariate polynomial. The pointwise
cone above a pure first-variable exponent has a separate description.

## References

* Mathlib, `Mathlib.Algebra.MvPolynomial.Equiv` (`finSuccEquiv`) and
  `Mathlib.RingTheory.MvPolynomial.MonomialOrder` (lex order and degree).
-/

set_option warningAsError true

namespace Finsupp

/-- Pointwise comparison with a pure first-variable exponent only tests the
first coordinate; the other coordinates are automatically nonnegative. -/
theorem cons_zero_le_cons_iff {n i d : ℕ} (β : Fin n →₀ ℕ) :
    ((0 : Fin n →₀ ℕ).cons d) ≤ β.cons i ↔ d ≤ i := by
  constructor
  · intro h
    exact (show d ≤ i from h 0)
  · intro hi index
    cases index using Fin.cases with
    | zero => simpa using hi
    | succ j => simp

end Finsupp

namespace MonomialOrder

/-- Lexicographic order prioritizes the first `Fin` variable: a smaller
first exponent lies below a pure first-variable exponent regardless of the tail. -/
theorem lex_le_cons_zero_of_le {n i d : ℕ} (β : Fin n →₀ ℕ)
    (hi : i ≤ d) (heq : i = d → β = 0) :
    (β.cons i) ≼[MonomialOrder.lex] ((0 : Fin n →₀ ℕ).cons d) := by
  rw [MonomialOrder.lex_le_iff]
  by_cases hlt : i < d
  · exact le_of_lt (Finsupp.Lex.lt_iff.mpr ⟨0, by simp, by simpa using hlt⟩)
  · have hid : i = d := le_antisymm hi (Nat.le_of_not_gt hlt)
    subst i
    rw [heq rfl]

/-- A nonzero scalar top coefficient of the polynomial obtained by separating
the first variable gives the maximum lexicographic exponent of the original
multivariate polynomial, including zero degree and no remaining variables. -/
theorem lex_degree_of_finSuccEquiv_scalar_top {K : Type*} [CommSemiring K]
    (n d : ℕ) (p : MvPolynomial (Fin (n + 1)) K) (c : K)
    (hdegree : (MvPolynomial.finSuccEquiv K n p).natDegree = d)
    (htop : (MvPolynomial.finSuccEquiv K n p).coeff d = MvPolynomial.C c)
    (hc : c ≠ 0) :
    (MonomialOrder.lex : MonomialOrder (Fin (n + 1))).degree p =
      (0 : Fin n →₀ ℕ).cons d := by
  classical
  let F := MvPolynomial.finSuccEquiv K n p
  have htopmem : ((0 : Fin n →₀ ℕ).cons d) ∈ p.support := by
    rw [MvPolynomial.mem_support_iff]
    have hcoeff := MvPolynomial.finSuccEquiv_coeff_coeff (0 : Fin n →₀ ℕ) p d
    rw [htop] at hcoeff
    rw [← hcoeff, MvPolynomial.coeff_zero_C]
    exact hc
  apply (MonomialOrder.lex : MonomialOrder (Fin (n + 1))).toSyn.injective
  apply le_antisymm
  · rw [MonomialOrder.degree_le_iff]
    intro exponent hexp
    rw [← Finsupp.cons_tail exponent]
    have hcoeff : (F.coeff (exponent 0)).coeff (Finsupp.tail exponent) ≠ 0 := by
      rw [MvPolynomial.finSuccEquiv_coeff_coeff, Finsupp.cons_tail]
      exact MvPolynomial.mem_support_iff.mp hexp
    apply lex_le_cons_zero_of_le
    · have hnonzero : F.coeff (exponent 0) ≠ 0 := by
        intro hzero
        exact hcoeff (by rw [hzero]; simp)
      exact (Polynomial.le_natDegree_of_ne_zero hnonzero).trans_eq hdegree
    · intro heq
      by_contra htail
      rw [heq, htop, MvPolynomial.coeff_C_of_ne_zero htail] at hcoeff
      exact hcoeff rfl
  · exact (MonomialOrder.lex : MonomialOrder (Fin (n + 1))).le_degree htopmem

end MonomialOrder
