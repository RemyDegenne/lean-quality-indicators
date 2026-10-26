/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!
# Degree under the one-variable polynomial equivalence

For a unique variable type, the canonical algebra equivalence with univariate polynomials
identifies multivariate total degree with univariate natural degree, including at zero.

The proof uses Mathlib's `MvPolynomial.coeff_uniqueAlgEquiv` to identify coefficients.
Each exponent's total weight is its sole coordinate, so Mathlib's coefficient and support
bounds give both degree inequalities without any nontriviality assumption on coefficients.

## References

This module builds on Mathlib's canonical polynomial equivalence and coefficient comparison
in `Mathlib.Algebra.MvPolynomial.Equiv`, and its support and degree APIs in
`Mathlib.Algebra.MvPolynomial.Degrees` and `Mathlib.Algebra.Polynomial.Degree.Lemmas`.
-/

@[expose] public section

universe u v

namespace MvPolynomial

/-- The canonical equivalence from polynomials in a unique variable to univariate polynomials
preserves natural degree: the image's `Polynomial.natDegree` is the original's `totalDegree`.
This holds for every commutative semiring, including the trivial semiring, and also at zero. -/
theorem natDegree_uniqueAlgEquiv
    {R : Type u} {σ : Type v} [CommSemiring R] [Unique σ]
    (p : MvPolynomial σ R) :
    Polynomial.natDegree (MvPolynomial.uniqueAlgEquiv R σ p) = p.totalDegree := by
  classical
  have hsum (d : σ →₀ ℕ) : d.sum (fun _ e => e) = d default :=
    Finsupp.sum_unique (fun _ => rfl)
  apply le_antisymm
  · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    rw [coeff_uniqueAlgEquiv]
    by_contra h
    have hd := le_totalDegree (mem_support_iff.mpr h)
    rw [hsum, Finsupp.single_eq_same] at hd
    exact (not_le_of_gt hn) hd
  · rw [totalDegree]
    apply Finset.sup_le
    intro d hd
    rw [hsum]
    apply Polynomial.le_natDegree_of_ne_zero
    rw [coeff_uniqueAlgEquiv, ← Finsupp.unique_single d]
    exact mem_support_iff.mp hd

end MvPolynomial
