/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.MvPolynomial.MonomialOrder
public import Mathlib.Algebra.MvPolynomial.Eval

@[expose] public section

/-!
# Monic lifts of multivariate polynomials

A surjective coefficient map admits monic polynomial lifts preserving the literal
leading exponent for any monomial order, including over the zero ring.

## References

* Riccardo Brasca's `Polynomial.lifts_and_natDegree_eq_and_monic` in Mathlib
  is a univariate analogue informing this distinct multivariate lift.
* Mathlib, `Mathlib.RingTheory.MvPolynomial.MonomialOrder`: Antoine
  Chambert-Loir's monomial-order and leading-coefficient infrastructure.
-/

set_option warningAsError true

namespace MonomialOrder

open MvPolynomial

variable {σ R S : Type*} [CommRing R] [CommRing S]

/-- Lift a monic multivariate polynomial along a surjective coefficient map,
preserving both its reduction and its leading exponent. Riccardo Brasca's
`Polynomial.lifts_and_natDegree_eq_and_monic` in Mathlib is a univariate
analogue; this is a separate multivariate proof. -/
theorem exists_monic_lift (m : MonomialOrder σ) (φ : R →+* S)
    (hφ : Function.Surjective φ) (p : MvPolynomial σ S) (hp : m.Monic p) :
    ∃ q : MvPolynomial σ R, map φ q = p ∧ m.Monic q ∧ m.degree q = m.degree p := by
  classical
  rcases subsingleton_or_nontrivial S with hS | hS
  · refine ⟨1, Subsingleton.elim _ _, m.monic_one, ?_⟩
    simp
  let lift : S → R := fun c => Classical.choose (hφ c)
  have hlift (c : S) : φ (lift c) = c := Classical.choose_spec (hφ c)
  let q : MvPolynomial σ R :=
    ∑ d ∈ p.support, monomial d (if d = m.degree p then 1 else lift (p.coeff d))
  have hcoeff (d : σ →₀ ℕ) :
      q.coeff d = if d ∈ p.support then
        (if d = m.degree p then 1 else lift (p.coeff d)) else 0 := by
    simp only [q, coeff_sum, coeff_monomial]
    simp
  have hdegree_mem : m.degree p ∈ p.support := by
    rw [mem_support_iff, hp.coeff_degree]
    exact one_ne_zero
  have hRone : (1 : R) ≠ 0 := by
    intro h
    exact (one_ne_zero : (1 : S) ≠ 0) (by simpa using congrArg φ h)
  have hmap : map φ q = p := by
    apply MvPolynomial.ext
    intro d
    rw [coeff_map, hcoeff]
    by_cases hd : d ∈ p.support
    · by_cases heq : d = m.degree p
      · subst d
        simp [hdegree_mem, hp.coeff_degree]
      · simp [hd, heq, hlift]
    · simp [hd, (notMem_support_iff.mp hd)]
  have hsupport : q.support = p.support := by
    ext d
    rw [mem_support_iff, hcoeff]
    by_cases hd : d ∈ p.support
    · by_cases heq : d = m.degree p
      · subst d
        simp [hdegree_mem, hRone]
      · have hliftne : lift (p.coeff d) ≠ 0 := by
          intro hzero
          apply mem_support_iff.mp hd
          rw [← hlift (p.coeff d), hzero, map_zero]
        simp [hd, heq, hliftne]
    · simp [hd]
  have hdegree : m.degree q = m.degree p := by
    unfold degree
    rw [hsupport]
  refine ⟨q, hmap, ?_, hdegree⟩
  rw [Monic, leadingCoeff, hdegree, hcoeff]
  simp [hdegree_mem]

end MonomialOrder
