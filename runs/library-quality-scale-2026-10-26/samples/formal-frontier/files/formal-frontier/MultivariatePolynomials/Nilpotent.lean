/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Copyright (c) 2023 Oliver Nash. All rights reserved.
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents, Andrew Yang, Emilie Uthaiwat, Oliver Nash
-/
module

public import Mathlib.Algebra.MvPolynomial.Nilpotent

/-!
# Nilpotent multivariate polynomials over commutative semirings

A multivariate polynomial over a commutative semiring is nilpotent if and only
if each of its coefficients is nilpotent. The variable type is arbitrary,
and the coefficient semiring may be trivial. Consequently,
`MvPolynomial.isReduced_iff` characterizes reduced polynomial semirings by
reducedness of their coefficients, and `MvPolynomial.instIsReducedOfCommSemiring`
provides the corresponding instance.

## References

* Mathlib, `Mathlib.Algebra.MvPolynomial.Nilpotent`, Andrew Yang's formalization
  of the coefficient criterion over commutative rings. The semiring criterion
  agrees with `MvPolynomial.isNilpotent_iff` over commutative rings.
* Mathlib, `Mathlib.RingTheory.Polynomial.Nilpotent`, Emilie Uthaiwat and Oliver
  Nash's formalization of the one-variable coefficient criterion.
-/

@[expose] public section

universe u v

/-- Adding a commuting nilpotent element does not change nilpotence. -/
theorem Commute.isNilpotent_add_right_iff {R : Type u} [Semiring R] {a b : R}
    (hcomm : Commute a b) (hb : IsNilpotent b) :
    IsNilpotent (a + b) ↔ IsNilpotent a := by
  refine ⟨?_, fun ha ↦ hcomm.isNilpotent_add ha hb⟩
  intro hab
  have hpow (k : ℕ) : ∃ c : R, Commute b c ∧ (a + b) ^ k = a ^ k + b * c := by
    induction k with
    | zero =>
        refine ⟨0, ?_, by simp⟩
        change b * 0 = 0 * b
        simp
    | succ k ih =>
        obtain ⟨c, hbc, hc⟩ := ih
        refine ⟨a ^ k + c * (a + b),
          (hcomm.symm.pow_right k).add_right
            (hbc.mul_right (hcomm.symm.add_right (Commute.refl b))), ?_⟩
        rw [pow_succ, hc]
        simp only [pow_succ, add_mul, mul_add, mul_assoc,
          (hcomm.pow_left k).eq, add_assoc]
        exact congrArg (fun x : R => a ^ k * a + x)
          (add_left_comm (b * (c * a)) (b * a ^ k) (b * (c * b)))
  obtain ⟨m, hm⟩ := hab
  obtain ⟨c, hbc, hc⟩ := hpow m
  have hz : a ^ m + b * c = 0 := hc.symm.trans hm
  -- If two elements sum to zero, their squares agree, even without subtraction.
  have hsq : (a ^ m) ^ 2 = (b * c) ^ 2 := by
    calc
      (a ^ m) ^ 2 = (a ^ m) ^ 2 + (a ^ m + b * c) * (b * c) := by
        rw [hz, zero_mul, add_zero]
      _ = a ^ m * (a ^ m + b * c) + (b * c) ^ 2 := by
        simp only [pow_two, add_mul, mul_add, add_assoc]
      _ = (b * c) ^ 2 := by rw [hz, mul_zero, zero_add]
  obtain ⟨n, hn⟩ := hb
  refine ⟨m * (2 * n), ?_⟩
  calc
    a ^ (m * (2 * n)) = ((a ^ m) ^ 2) ^ n := by simp only [pow_mul]
    _ = ((b * c) ^ 2) ^ n := by rw [hsq]
    _ = ((b * c) ^ n) ^ 2 := by rw [← pow_mul, Nat.mul_comm 2 n, pow_mul]
    _ = 0 := by rw [hbc.mul_pow, hn, zero_mul]; simp

namespace Polynomial

private theorem isNilpotent_iff_coeff {R : Type u} [CommSemiring R]
    (p : Polynomial R) : IsNilpotent p ↔ ∀ i : ℕ, IsNilpotent (p.coeff i) := by
  refine
    ⟨p.recOnHorner (by simp) (fun q r hq₀ _ hq hqr i ↦ ?_)
      (fun q _ hq hqX i ↦ ?_), fun h ↦ ?_⟩
  · rw [← sum_monomial_eq p]
    exact isNilpotent_sum (fun i _ ↦ by simpa only [isNilpotent_monomial_iff] using h i)
  · have hr : IsNilpotent (C r) := by
      obtain ⟨k, hk⟩ := hqr
      replace hq : eval 0 q = 0 := by rwa [coeff_zero_eq_aeval_zero] at hq₀
      refine isNilpotent_C_iff.mpr ⟨k, ?_⟩
      simpa [coeff_zero_eq_aeval_zero, hq] using congr_arg (fun q ↦ coeff q 0) hk
    rcases i with - | i
    · simpa [hq₀] using hr
    simp only [coeff_add, coeff_C_succ, add_zero]
    apply hq
    exact ((Commute.all q (C r)).isNilpotent_add_right_iff hr).mp hqr
  · rcases i with - | i
    · simp
    simpa using hq (isNilpotent_mul_X_iff.mp hqX) i

private theorem isNilpotent_iff_coeff_eq_isNilpotent_iff {R : Type u} [CommRing R]
    (p : Polynomial R) :
    isNilpotent_iff_coeff p = (Polynomial.isNilpotent_iff (P := p)) := by
  exact Subsingleton.elim _ _

end Polynomial

namespace MvPolynomial

variable {R : Type u} {σ : Type v}

private theorem isNilpotent_iff_coeff_of_finite [CommSemiring R] [Finite σ]
    (p : MvPolynomial σ R) :
    IsNilpotent p ↔ ∀ d : σ →₀ ℕ, IsNilpotent (p.coeff d) := by
  classical
  -- Keep the chosen fintype local to the induction, as in Mathlib's ring proof.
  refine have := Fintype.ofFinite σ; Fintype.induction_empty_option ?_ ?_ ?_ σ p
  · intro α β _ e h p
    rw [← IsNilpotent.map_iff (rename_injective _ e.symm.injective), h,
      (Finsupp.equivCongrLeft e).forall_congr_left]
    simp [Finsupp.equivMapDomain_eq_mapDomain, coeff_rename_mapDomain _ e.symm.injective]
  · simp [Unique.forall_iff, ← IsNilpotent.map_iff (isEmptyRingEquiv R PEmpty).injective,
      -isEmptyRingEquiv_apply, isEmptyRingEquiv_eq_coeff_zero]
  · intro α _ h p
    obtain ⟨p, rfl⟩ := (optionEquivLeft _ _).symm.surjective p
    simp [IsNilpotent.map_iff (optionEquivLeft _ _).symm.injective,
      Polynomial.isNilpotent_iff_coeff, h, Finsupp.optionEquiv.forall_congr_left,
      ← optionEquivLeft_coeff_some_coeff_none, Finsupp.coe_update]

/-- A multivariate polynomial over a commutative semiring is nilpotent exactly
when all of its coefficients are nilpotent. No finiteness assumption on the
variable type is required. This generalizes Mathlib's
`MvPolynomial.isNilpotent_iff` for commutative rings. -/
theorem isNilpotent_iff_coeff [CommSemiring R] (p : MvPolynomial σ R) :
    IsNilpotent p ↔ ∀ d : σ →₀ ℕ, IsNilpotent (p.coeff d) := by
  obtain ⟨n, f, hf, p, rfl⟩ := p.exists_fin_rename
  rw [IsNilpotent.map_iff (rename_injective _ hf), isNilpotent_iff_coeff_of_finite]
  lift f to Fin n ↪ σ using hf
  refine ⟨fun h d ↦ ?_, fun h d ↦ by simpa using h (d.embDomain f)⟩
  by_cases hd : d ∈ Set.range (Finsupp.embDomain f)
  · aesop
  · rw [coeff_rename_eq_zero] <;> aesop (add simp Finsupp.embDomain_eq_mapDomain)

private theorem isNilpotent_iff_coeff_eq_isNilpotent_iff [CommRing R]
    (p : MvPolynomial σ R) :
    isNilpotent_iff_coeff p = (MvPolynomial.isNilpotent_iff (P := p)) := by
  exact Subsingleton.elim _ _

/-- A multivariate polynomial semiring is reduced exactly when its coefficient
semiring is reduced, with no restriction on the variable type. -/
@[simp]
theorem isReduced_iff [CommSemiring R] :
    IsReduced (MvPolynomial σ R) ↔ IsReduced R := by
  constructor
  · intro h
    letI : IsReduced (MvPolynomial σ R) := h
    exact isReduced_of_injective (C : R →+* MvPolynomial σ R) (C_injective σ R)
  · intro h
    letI : IsReduced R := h
    refine ⟨fun p hp ↦ ?_⟩
    ext d
    simpa using ((isNilpotent_iff_coeff p).mp hp d).eq_zero

-- The inferred instance here is Mathlib's instance for commutative rings.
private theorem isReduced_iff_mpr_eq [CommRing R] [IsReduced R] :
    (isReduced_iff (σ := σ) (R := R)).mpr ‹IsReduced R› =
      (inferInstance : IsReduced (MvPolynomial σ R)) := by
  exact Subsingleton.elim _ _

/-- Multivariate polynomials over a reduced commutative semiring form a reduced semiring. -/
instance instIsReducedOfCommSemiring [CommSemiring R] [IsReduced R] :
    IsReduced (MvPolynomial σ R) :=
  (isReduced_iff (σ := σ) (R := R)).mpr inferInstance

end MvPolynomial
