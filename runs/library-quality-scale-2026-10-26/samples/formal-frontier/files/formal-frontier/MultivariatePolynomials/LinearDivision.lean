/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.MvPolynomial.Groebner

set_option warningAsError true

/-!
# Fixed linear division of multivariate polynomials

For a family of polynomials with invertible leading coefficients, the division
theorem supplies a quotient family and a reduced remainder for each basis
monomial. Choosing these witnesses once, and extending them by linearity, gives
fixed linear quotient and remainder operators. The witnesses for monomials
outside all leading cones are chosen to be trivial.

## References

* Mathlib, `Mathlib.RingTheory.MvPolynomial.Groebner`: Antoine Chambert-Loir's
  `MonomialOrder.div` and reduced-remainder infrastructure. The fixed linear
  operators are a separate construction from its existential division theorem.
-/

@[expose] public section

namespace MonomialOrder

open MvPolynomial

variable {σ ι R : Type*} [CommRing R]

/-- The chosen witness on a basis monomial, with an explicit trivial reduced branch.
Uses Antoine Chambert-Loir's `MonomialOrder.div` in Mathlib for the nontrivial branch. -/
noncomputable def basisDivision (m : MonomialOrder σ)
    (b : ι → MvPolynomial σ R) (hb : ∀ i, IsUnit (m.leadingCoeff (b i)))
    (α : σ →₀ ℕ) :
    { gr : (ι →₀ MvPolynomial σ R) × MvPolynomial σ R //
      monomial α (1 : R) = Finsupp.linearCombination (MvPolynomial σ R) b gr.1 + gr.2 ∧
      (∀ β ∈ gr.2.support, ∀ i, ¬ m.degree (b i) ≤ β) ∧
      ((∀ i, ¬ m.degree (b i) ≤ α) → gr.1 = 0 ∧ gr.2 = monomial α 1) } := by
  classical
  by_cases hα : ∀ i, ¬ m.degree (b i) ≤ α
  · refine ⟨(0, monomial α 1), ?_, ?_, ?_⟩
    · simp
    · intro β hβ i
      have hβα : β = α := by
        by_contra hne
        have hzero : (monomial α (1 : R)).coeff β = 0 := by
          simp [coeff_monomial, Ne.symm hne]
        exact (Finsupp.mem_support_iff.mp hβ) hzero
      exact hβα ▸ hα i
    · intro _
      exact ⟨rfl, rfl⟩
  · let g := Classical.choose (m.div hb (monomial α (1 : R)))
    let r := Classical.choose (Classical.choose_spec (m.div hb (monomial α (1 : R))))
    have hgr := Classical.choose_spec
      (Classical.choose_spec (m.div hb (monomial α (1 : R))))
    exact ⟨(g, r), hgr.1, hgr.2.2, fun h => (hα h).elim⟩

/-- Fixed, finitely supported quotient operator obtained from monomial division. -/
noncomputable def linearDivisionQuotient (m : MonomialOrder σ)
    (b : ι → MvPolynomial σ R) (hb : ∀ i, IsUnit (m.leadingCoeff (b i))) :
    MvPolynomial σ R →ₗ[R] (ι →₀ MvPolynomial σ R) :=
  (Finsupp.linearCombination R (fun α => (basisDivision m b hb α).1.1)).comp
    (AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap

/-- Fixed reduced-remainder operator obtained from monomial division. -/
noncomputable def linearDivisionRemainder (m : MonomialOrder σ)
    (b : ι → MvPolynomial σ R) (hb : ∀ i, IsUnit (m.leadingCoeff (b i))) :
    MvPolynomial σ R →ₗ[R] MvPolynomial σ R :=
  (Finsupp.linearCombination R (fun α => (basisDivision m b hb α).1.2)).comp
    (AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap

lemma monomial_eq_smul_one (α : σ →₀ ℕ) (a : R) :
    monomial α a = a • (monomial α (1 : R)) := by
  rw [smul_monomial, smul_eq_mul, mul_one]

theorem linearDivisionQuotient_monomial (m : MonomialOrder σ)
    (b : ι → MvPolynomial σ R) (hb : ∀ i, IsUnit (m.leadingCoeff (b i)))
    (α : σ →₀ ℕ) :
    linearDivisionQuotient m b hb (monomial α (1 : R)) = (basisDivision m b hb α).1.1 := by
  simp [linearDivisionQuotient, monomial]

theorem linearDivisionRemainder_monomial (m : MonomialOrder σ)
    (b : ι → MvPolynomial σ R) (hb : ∀ i, IsUnit (m.leadingCoeff (b i)))
    (α : σ →₀ ℕ) :
    linearDivisionRemainder m b hb (monomial α (1 : R)) = (basisDivision m b hb α).1.2 := by
  simp [linearDivisionRemainder, monomial]

/-- The chosen quotient and remainder reconstruct the input polynomial. -/
theorem linearDivision_decomposition (m : MonomialOrder σ)
    (b : ι → MvPolynomial σ R) (hb : ∀ i, IsUnit (m.leadingCoeff (b i)))
    (p : MvPolynomial σ R) :
    p = Finsupp.linearCombination (MvPolynomial σ R) b (linearDivisionQuotient m b hb p) +
      linearDivisionRemainder m b hb p := by
  classical
  have hsmul (a : R) (g : ι →₀ MvPolynomial σ R) :
      Finsupp.linearCombination (MvPolynomial σ R) b (a • g) =
        a • Finsupp.linearCombination (MvPolynomial σ R) b g :=
    (Finsupp.linearCombination (MvPolynomial σ R) b).map_smul_of_tower a g
  calc
    p = ∑ α ∈ p.support, monomial α (p.coeff α) := p.as_sum
    _ = ∑ α ∈ p.support,
        (Finsupp.linearCombination (MvPolynomial σ R) b
            (linearDivisionQuotient m b hb (monomial α (p.coeff α))) +
          linearDivisionRemainder m b hb (monomial α (p.coeff α))) := by
      apply Finset.sum_congr rfl
      intro α _
      calc
        monomial α (p.coeff α) = (p.coeff α) • monomial α (1 : R) :=
          monomial_eq_smul_one α (p.coeff α)
        _ = (p.coeff α) • (Finsupp.linearCombination (MvPolynomial σ R) b
              (basisDivision m b hb α).1.1 + (basisDivision m b hb α).1.2) :=
          congrArg ((p.coeff α) • ·) (basisDivision m b hb α).2.1
        _ = _ := by
          simp only [monomial_eq_smul_one α (p.coeff α), map_smul,
            linearDivisionQuotient_monomial, linearDivisionRemainder_monomial,
            hsmul, smul_add]
    _ = Finsupp.linearCombination (MvPolynomial σ R) b
          (linearDivisionQuotient m b hb (∑ α ∈ p.support, monomial α (p.coeff α))) +
        linearDivisionRemainder m b hb (∑ α ∈ p.support, monomial α (p.coeff α)) := by
      rw [map_sum, map_sum, map_sum, Finset.sum_add_distrib]
    _ = _ := by rw [support_sum_monomial_coeff]

/-- Polynomials whose actual exponents avoid all the leading cones. -/
def reducedSubmodule (m : MonomialOrder σ) (b : ι → MvPolynomial σ R) :
    Submodule R (MvPolynomial σ R) where
  carrier := {p | ∀ α i, m.degree (b i) ≤ α → p.coeff α = 0}
  zero_mem' := by intro α i _; simp
  add_mem' := by
    intro p q hp hq α i hi
    simp [hp α i hi, hq α i hi]
  smul_mem' := by
    intro a p hp α i hi
    simp [hp α i hi]

theorem basisDivision_reduced (m : MonomialOrder σ)
    (b : ι → MvPolynomial σ R) (hb : ∀ i, IsUnit (m.leadingCoeff (b i)))
    (α : σ →₀ ℕ) : (basisDivision m b hb α).1.2 ∈ reducedSubmodule m b := by
  intro β i hi
  by_contra hne
  exact (basisDivision m b hb α).2.2.1 β
    (Finsupp.mem_support_iff.mpr hne) i hi

/-- Every actual exponent in the fixed remainder avoids every leading cone,
using the componentwise order on finitely supported exponent vectors. -/
theorem linearDivision_remainder_support (m : MonomialOrder σ)
    (b : ι → MvPolynomial σ R) (hb : ∀ i, IsUnit (m.leadingCoeff (b i)))
    (p : MvPolynomial σ R) :
    ∀ α ∈ (linearDivisionRemainder m b hb p).support,
      ∀ i, ¬ m.degree (b i) ≤ α := by
  have hr : linearDivisionRemainder m b hb p ∈ reducedSubmodule m b := by
    classical
    change Finsupp.linearCombination R (fun α => (basisDivision m b hb α).1.2)
      ((AddMonoidAlgebra.coeffLinearEquiv R) p) ∈ _
    rw [Finsupp.linearCombination_apply]
    exact Submodule.sum_mem _ (fun α _ =>
      (reducedSubmodule m b).smul_mem (((AddMonoidAlgebra.coeffLinearEquiv R) p) α)
        (basisDivision_reduced m b hb α))
  intro α hα i hi
  exact (Finsupp.mem_support_iff.mp hα) (hr α i hi)

theorem linearMap_preserves_coeffsIn (J : Ideal R)
    (F : MvPolynomial σ R →ₗ[R] MvPolynomial σ R)
    (p : MvPolynomial σ R) (hp : p ∈ coeffsIn σ (J : Submodule R R)) :
    F p ∈ coeffsIn σ (J : Submodule R R) := by
  classical
  rw [p.as_sum]
  rw [map_sum]
  apply Submodule.sum_mem _
  intro α _
  rw [monomial_eq_smul_one, map_smul]
  rw [mem_coeffsIn] at hp ⊢
  intro β
  rw [coeff_smul, smul_eq_mul]
  exact J.mul_mem_right _ (hp α)

/-- Every coefficient ideal is preserved by the chosen remainder operator. -/
theorem linearDivision_remainder_coeffsIn (m : MonomialOrder σ)
    (b : ι → MvPolynomial σ R) (hb : ∀ i, IsUnit (m.leadingCoeff (b i)))
    (J : Ideal R) (p : MvPolynomial σ R)
    (hp : p ∈ coeffsIn σ (J : Submodule R R)) :
    linearDivisionRemainder m b hb p ∈ coeffsIn σ (J : Submodule R R) :=
  linearMap_preserves_coeffsIn J (linearDivisionRemainder m b hb) p hp

/-- Every coefficient ideal is preserved in every quotient coordinate. -/
theorem linearDivision_quotient_coeffsIn (m : MonomialOrder σ)
    (b : ι → MvPolynomial σ R) (hb : ∀ i, IsUnit (m.leadingCoeff (b i)))
    (J : Ideal R) (p : MvPolynomial σ R)
    (hp : p ∈ coeffsIn σ (J : Submodule R R)) (i : ι) :
    (linearDivisionQuotient m b hb p) i ∈ coeffsIn σ (J : Submodule R R) := by
  simpa only [LinearMap.comp_apply, Finsupp.lapply_apply] using
    linearMap_preserves_coeffsIn J
      ((Finsupp.lapply i).comp (linearDivisionQuotient m b hb)) p hp

/-- An already reduced input is fixed by the chosen remainder operator. -/
theorem linearDivision_remainder_of_reduced (m : MonomialOrder σ)
    (b : ι → MvPolynomial σ R) (hb : ∀ i, IsUnit (m.leadingCoeff (b i)))
    (p : MvPolynomial σ R) (hp : ∀ α ∈ p.support, ∀ i, ¬ m.degree (b i) ≤ α) :
    linearDivisionRemainder m b hb p = p := by
  classical
  calc
    linearDivisionRemainder m b hb p =
        ∑ α ∈ p.support, linearDivisionRemainder m b hb (monomial α (p.coeff α)) := by
          conv_lhs => rw [p.as_sum]
          rw [map_sum]
    _ = ∑ α ∈ p.support, monomial α (p.coeff α) := by
      apply Finset.sum_congr rfl
      intro α hα
      rw [monomial_eq_smul_one, map_smul]
      rw [linearDivisionRemainder_monomial]
      exact congrArg ((p.coeff α) • ·) ((basisDivision m b hb α).2.2.2 (hp α hα)).2
    _ = p := (p.as_sum).symm

/-- An already reduced input has zero chosen quotient. -/
theorem linearDivision_quotient_of_reduced (m : MonomialOrder σ)
    (b : ι → MvPolynomial σ R) (hb : ∀ i, IsUnit (m.leadingCoeff (b i)))
    (p : MvPolynomial σ R) (hp : ∀ α ∈ p.support, ∀ i, ¬ m.degree (b i) ≤ α) :
    linearDivisionQuotient m b hb p = 0 := by
  classical
  rw [p.as_sum, map_sum]
  apply Finset.sum_eq_zero
  intro α hα
  rw [monomial_eq_smul_one, map_smul]
  rw [linearDivisionQuotient_monomial]
  rw [((basisDivision m b hb α).2.2.2 (hp α hα)).1]
  simp

end MonomialOrder
