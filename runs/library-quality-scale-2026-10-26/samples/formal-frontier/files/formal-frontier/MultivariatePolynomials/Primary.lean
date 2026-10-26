/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MultivariatePolynomials.CoefficientIdeal
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Data.Fintype.Option
public import Mathlib.RingTheory.Ideal.IsPrimary
public import Mathlib.RingTheory.Polynomial.Nilpotent

/-!
# Primary coefficient ideals

Extension along the constant-polynomial homomorphism preserves and reflects
primary ideals of a commutative ring. The coefficient and variable universes
are independent; the ideal may be the top ideal and the variable type may be
empty.

For persistence, pass to the quotient by the coefficient ideal. In one
variable, McCoy's theorem supplies a nonzero scalar annihilating a polynomial
zero divisor. Primaryness of zero makes each coefficient nilpotent, and the
polynomial nilpotence criterion then applies. Empty and option variable
sets give finite-variable persistence by induction. A joint finite-variable
presentation of two polynomials gives the unrestricted result. Contraction
along `C` gives reflection.

## References

* Mathlib's `Mathlib.Algebra.Polynomial.AlgebraMap`, by Chris Hughes,
  Johannes Hölzl, Kim Morrison and Jens Wagemaker, supplies the univariate
  McCoy theorem `Polynomial.notMem_nonZeroDivisors_iff`.
* `Mathlib.RingTheory.Polynomial.Nilpotent`, by Emilie Uthaiwat and Oliver
  Nash (copyright 2023 Oliver Nash), supplies `Polynomial.isNilpotent_iff`.
* `Mathlib.Algebra.MvPolynomial.Nilpotent`, by Andrew Yang (copyright 2025
  Andrew Yang), provides the finite-variable induction pattern used here.
  These Mathlib sources are released under the Apache 2.0 license.
* `Mathlib.Algebra.MvPolynomial.Rename` supplies the joint finite-variable
  presentation `exists_finset_rename₂`; `Mathlib.Algebra.MvPolynomial.Equiv`
  supplies the empty-variable and option-variable equivalences.
* `Mathlib.RingTheory.Ideal.IsPrimary`, by Kenny Lau and Yakov Pechersky,
  supplies the stock primary criterion and contraction theorem. The
  quotient kernel and coefficient kernel APIs identify the extended ideal.
-/

@[expose] public section

universe u v

namespace MvPolynomial

variable {R : Type u} {σ : Type v} [CommRing R]

private theorem isPrimary_bot_polynomial (hR : (⊥ : Ideal R).IsPrimary) :
    (⊥ : Ideal (Polynomial R)).IsPrimary := by
  refine Ideal.isPrimary_iff.mpr ⟨?_, ?_⟩
  · intro htop
    apply hR.ne_top
    have hc := congrArg (Ideal.comap (Polynomial.C : R →+* Polynomial R)) htop
    simpa only [Ideal.comap_bot_of_injective
      (Polynomial.C : R →+* Polynomial R) Polynomial.C_injective,
      Ideal.comap_top] using hc
  · intro f g hfg
    by_cases hf : f ∈ (⊥ : Ideal (Polynomial R))
    · exact Or.inl hf
    right
    have hf0 : f ≠ 0 := by simpa only [Submodule.mem_bot] using hf
    have hfg0 : f * g = 0 := by simpa only [Submodule.mem_bot] using hfg
    have hg : g ∉ nonZeroDivisors (Polynomial R) :=
      notMem_nonZeroDivisors_iff_right.mpr ⟨f, hfg0, hf0⟩
    obtain ⟨a, ha, hag⟩ := Polynomial.notMem_nonZeroDivisors_iff.mp hg
    have hnil : IsNilpotent g := Polynomial.isNilpotent_iff.mpr fun n => by
      have hac : a * g.coeff n ∈ (⊥ : Ideal R) := by
        rw [Submodule.mem_bot]
        simpa only [Polynomial.coeff_smul, Polynomial.coeff_zero, smul_eq_mul] using
          congrArg (fun p : Polynomial R => p.coeff n) hag
      rcases (Ideal.isPrimary_iff.mp hR).2 hac with hazero | hcoeff
      · exact False.elim (ha (by simpa only [Submodule.mem_bot] using hazero))
      · rcases Ideal.mem_radical_iff.mp hcoeff with ⟨k, hk⟩
        exact ⟨k, by simpa only [Submodule.mem_bot] using hk⟩
    rcases hnil with ⟨n, hn⟩
    exact Ideal.mem_radical_iff.mpr ⟨n, by simpa only [Submodule.mem_bot] using hn⟩

private theorem isPrimary_bot_mvPolynomial_of_finite [Finite σ]
    (hR : (⊥ : Ideal R).IsPrimary) :
    (⊥ : Ideal (MvPolynomial σ R)).IsPrimary := by
  refine Finite.induction_empty_option
    (P := fun τ : Type v => (⊥ : Ideal (MvPolynomial τ R)).IsPrimary) ?_ ?_ ?_ σ
  · intro α β e h
    simpa only [Ideal.comap_bot_of_injective
      (renameEquiv R e.symm).toRingHom (renameEquiv R e.symm).injective] using
      h.comap (renameEquiv R e.symm).toRingHom
  · simpa only [Ideal.comap_bot_of_injective
      (isEmptyRingEquiv R PEmpty).toRingHom (isEmptyRingEquiv R PEmpty).injective] using
      hR.comap (isEmptyRingEquiv R PEmpty).toRingHom
  · intro α _ h
    simpa only [Ideal.comap_bot_of_injective
      (optionEquivLeft R α).toRingHom (optionEquivLeft R α).injective] using
      (isPrimary_bot_polynomial h).comap (optionEquivLeft R α).toRingHom

private theorem isPrimary_bot_mvPolynomial (hR : (⊥ : Ideal R).IsPrimary) :
    (⊥ : Ideal (MvPolynomial σ R)).IsPrimary := by
  classical
  refine Ideal.isPrimary_iff.mpr ⟨?_, ?_⟩
  · intro htop
    apply hR.ne_top
    have hc := congrArg (Ideal.comap (C : R →+* MvPolynomial σ R)) htop
    simpa only [Ideal.comap_bot_of_injective
      (C : R →+* MvPolynomial σ R) (C_injective σ R), Ideal.comap_top] using hc
  · intro f g hfg
    obtain ⟨s, p, q, rfl, rfl⟩ := exists_finset_rename₂ f g
    have hpq : p * q ∈ (⊥ : Ideal (MvPolynomial s R)) := by
      rw [Submodule.mem_bot]
      apply rename_injective (Subtype.val : s → σ) Subtype.val_injective
      simpa only [map_mul, map_zero, Submodule.mem_bot] using hfg
    rcases (Ideal.isPrimary_iff.mp
      (isPrimary_bot_mvPolynomial_of_finite (σ := s) hR)).2 hpq with hp | hq
    · left
      rw [Submodule.mem_bot] at hp ⊢
      rw [hp, map_zero]
    · right
      rcases Ideal.mem_radical_iff.mp hq with ⟨n, hn⟩
      refine Ideal.mem_radical_iff.mpr ⟨n, ?_⟩
      rw [Submodule.mem_bot] at hn ⊢
      simpa only [map_pow, map_zero] using
        congrArg (rename (Subtype.val : s → σ)) hn

/-- A coefficient ideal is primary if and only if its extension to multivariate
polynomials is primary. -/
theorem isPrimary_map_C_iff (I : Ideal R) :
    (I.map (C : R →+* MvPolynomial σ R)).IsPrimary ↔ I.IsPrimary := by
  constructor
  · intro h
    simpa only [comap_map_C] using h.comap (C : R →+* MvPolynomial σ R)
  · intro hI
    letI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI.ne_top
    have hquot : (⊥ : Ideal (R ⧸ I)).IsPrimary := by
      refine Ideal.isPrimary_iff.mpr ⟨bot_ne_top, ?_⟩
      intro x y hxy
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective (I := I) x
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective (I := I) y
      have hab : a * b ∈ I := by
        apply Ideal.Quotient.eq_zero_iff_mem.mp
        simpa only [map_mul, Submodule.mem_bot] using hxy
      rcases (Ideal.isPrimary_iff.mp hI).2 hab with ha | hb
      · left
        rw [Submodule.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
        exact ha
      · right
        rcases Ideal.mem_radical_iff.mp hb with ⟨n, hn⟩
        refine Ideal.mem_radical_iff.mpr ⟨n, ?_⟩
        rw [Submodule.mem_bot, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
        exact hn
    have hpoly := isPrimary_bot_mvPolynomial (σ := σ) hquot
    have hker :
        RingHom.ker (map (Ideal.Quotient.mk I) :
          MvPolynomial σ R →+* MvPolynomial σ (R ⧸ I)) =
        I.map (C : R →+* MvPolynomial σ R) := by
      have hmk : RingHomClass.toRingHom (Ideal.Quotient.mk I) = Ideal.Quotient.mk I :=
        RingHom.coe_inj (RingHom.coe_coe (Ideal.Quotient.mk I))
      simpa only [hmk, Ideal.mk_ker] using
        (ker_map_eq_map_C (σ := σ) (F := R →+* R ⧸ I) (Ideal.Quotient.mk I))
    rw [← hker, RingHom.ker_eq_comap_bot]
    exact hpoly.comap (map (Ideal.Quotient.mk I))

end MvPolynomial
