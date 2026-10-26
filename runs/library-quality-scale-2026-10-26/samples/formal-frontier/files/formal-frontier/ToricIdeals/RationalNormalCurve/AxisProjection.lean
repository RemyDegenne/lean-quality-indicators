/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.RingTheory.Ideal.Quotient.Operations
public import ToricIdeals.RationalNormalCurve

/-!
# Coordinate-axis projection of a rational-normal-curve quotient

For a commutative ring `R` and every degree `n`, `axisProjection R n` sends the
class of `X₀` in the Hankel quotient to `Polynomial.X`, sends every other
coordinate to zero, and preserves coefficients. Its section `axisSection R n`
embeds a univariate polynomial using the first quotient coordinate.

The projection is a split surjection and the section is injective. Maps from
the quotient are determined by all their coordinate images. Those killing
every coordinate other than `X₀` factor through the projection, with the image
of `X₀` prescribing the resulting polynomial evaluation.

At degree zero there are no Hankel minors, so the projection is bijective and
the section is also a left inverse. The degree-zero quotient is the full
one-variable polynomial ring, not the quotient by the monomial parametrization
kernel: that parametrization sends `X₀` to `1`, whereas this projection retains
an indeterminate. No inverse on the entire quotient is asserted in positive
degree. The constructions include zero coefficient rings and rings with
nilpotent elements.

## References

* Formal Frontier Agents, `ToricIdeals.RationalNormalCurve`, for the Hankel
  presentation and its degree-zero and degree-one boundaries.
* Formal Frontier Agents, `ToricIdeals.RationalNormalCurve.Artinian`, for the
  coordinate-axis evaluation, polynomial section and quotient surjection.
* Mathlib contributors, `Mathlib.Algebra.MvPolynomial.Eval`,
  `Mathlib.Algebra.Polynomial.AlgebraMap` and
  `Mathlib.RingTheory.Ideal.Quotient.Operations`, for algebra evaluation,
  quotient lifts and homomorphism extensionality.
-/

@[expose] public section

universe u v

namespace ToricIdeals.RationalNormalCurve

variable (R : Type u) [CommRing R]

section

variable (n : ℕ)

/-- The quotient algebra map retaining the first coordinate as an indeterminate
and sending every other coordinate to zero. Coefficients are preserved, in every
degree and over every commutative coefficient ring. -/
noncomputable def axisProjection :
    (Source R n ⧸ hankelIdeal R n) →ₐ[R] Polynomial R :=
  Ideal.Quotient.liftₐ (hankelIdeal R n)
    (MvPolynomial.aeval
      (fun i : Fin (n + 1) => if i = 0 then Polynomial.X else 0))
    (by
      classical
      have hle : hankelIdeal R n ≤ RingHom.ker
          (MvPolynomial.aeval
            (fun i : Fin (n + 1) => if i = 0 then Polynomial.X else 0) :
            Source R n →ₐ[R] Polynomial R).toRingHom := by
        apply Ideal.span_le.2
        rintro _ ⟨p, rfl⟩
        apply RingHom.mem_ker.mpr
        change MvPolynomial.aeval
          (fun i : Fin (n + 1) => if i = 0 then Polynomial.X else 0)
          (hankelMinor R n p) = 0
        simp only [hankelMinor, map_sub, map_mul, MvPolynomial.aeval_X,
          Fin.succ_ne_zero, ↓reduceIte, mul_zero, zero_mul, sub_self]
      intro f hf
      exact hle hf)

/-- Embed a univariate polynomial in the Hankel quotient by evaluating its
indeterminate at the first quotient coordinate. -/
noncomputable def axisSection :
    Polynomial R →ₐ[R] (Source R n ⧸ hankelIdeal R n) :=
  (Ideal.Quotient.mkₐ R (hankelIdeal R n)).comp
    (Polynomial.aeval (MvPolynomial.X (0 : Fin (n + 1)) : Source R n))

/-- On a quotient representative, the axis projection is evaluation at
`(Polynomial.X, 0, …, 0)`. -/
@[simp] theorem axisProjection_mk (f : Source R n) :
    axisProjection R n (Ideal.Quotient.mk (hankelIdeal R n) f) =
      MvPolynomial.aeval
        (fun i : Fin (n + 1) => if i = 0 then Polynomial.X else 0) f := by
  rfl

/-- Composing the axis projection with the quotient map gives coordinate-axis
evaluation on the multivariate polynomial ring. -/
theorem axisProjection_comp_mk :
    (axisProjection R n).comp (Ideal.Quotient.mkₐ R (hankelIdeal R n)) =
      MvPolynomial.aeval
        (fun i : Fin (n + 1) => if i = 0 then Polynomial.X else 0) := by
  unfold axisProjection
  exact Ideal.Quotient.liftₐ_comp _ _ _

/-- The axis projection preserves the class of each constant polynomial. -/
@[simp] theorem axisProjection_C (r : R) :
    axisProjection R n
      (Ideal.Quotient.mk (hankelIdeal R n) (MvPolynomial.C r)) = Polynomial.C r := by
  simp only [axisProjection_mk, MvPolynomial.aeval_C, Polynomial.algebraMap_eq]

/-- The canonical coefficient map into the quotient is sent to polynomial
constants by the axis projection. -/
@[simp] theorem axisProjection_algebraMap (r : R) :
    axisProjection R n
      (algebraMap R (Source R n ⧸ hankelIdeal R n) r) = Polynomial.C r := by
  simpa only [Polynomial.algebraMap_eq] using (axisProjection R n).commutes r

/-- The first coordinate is sent to the polynomial indeterminate, and every
other coordinate is sent to zero. -/
@[simp] theorem axisProjection_X (i : Fin (n + 1)) :
    axisProjection R n
      (Ideal.Quotient.mk (hankelIdeal R n) (MvPolynomial.X i)) =
      if i = 0 then Polynomial.X else 0 := by
  rw [axisProjection_mk, MvPolynomial.aeval_X]

/-- The class of the first coordinate maps to `Polynomial.X`. -/
@[simp] theorem axisProjection_X_zero :
    axisProjection R n
      (Ideal.Quotient.mk (hankelIdeal R n) (MvPolynomial.X (0 : Fin (n + 1)))) =
      Polynomial.X := by
  simp only [axisProjection_X, ↓reduceIte]

/-- Every coordinate with nonzero index vanishes under the axis projection. -/
@[simp] theorem axisProjection_X_of_ne_zero (i : Fin (n + 1)) (hi : i ≠ 0) :
    axisProjection R n
      (Ideal.Quotient.mk (hankelIdeal R n) (MvPolynomial.X i)) = 0 := by
  simp only [axisProjection_X, hi, ↓reduceIte]

/-- The polynomial section sends constants to their quotient classes. -/
@[simp] theorem axisSection_C (r : R) :
    axisSection R n (Polynomial.C r) =
      Ideal.Quotient.mk (hankelIdeal R n) (MvPolynomial.C r) := by
  simp only [axisSection, AlgHom.comp_apply, Polynomial.aeval_C,
    MvPolynomial.algebraMap_eq, Ideal.Quotient.mkₐ_eq_mk]

/-- The polynomial section sends the indeterminate to the first quotient
coordinate. -/
@[simp] theorem axisSection_X :
    axisSection R n Polynomial.X =
      Ideal.Quotient.mk (hankelIdeal R n) (MvPolynomial.X (0 : Fin (n + 1))) := by
  simp only [axisSection, AlgHom.comp_apply, Polynomial.aeval_X,
    Ideal.Quotient.mkₐ_eq_mk]

/-- Projecting a polynomial embedded by the section recovers that polynomial. -/
@[simp] theorem axisProjection_axisSection (p : Polynomial R) :
    axisProjection R n (axisSection R n p) = p := by
  have h : (axisProjection R n).comp (axisSection R n) =
      AlgHom.id R (Polynomial R) := by
    apply Polynomial.algHom_ext
    simp only [AlgHom.comp_apply, axisSection_X, axisProjection_X_zero, AlgHom.id_apply]
  exact AlgHom.congr_fun h p

/-- The section is a right inverse of the axis projection as an algebra map. -/
theorem axisProjection_comp_axisSection :
    (axisProjection R n).comp (axisSection R n) = AlgHom.id R (Polynomial R) := by
  exact AlgHom.ext (axisProjection_axisSection R n)

/-- The coordinate-axis projection is a split surjection in every degree.
Its section gives a preimage for each univariate polynomial. -/
theorem axisProjection_surjective : Function.Surjective (axisProjection R n) := by
  have h : Function.RightInverse (axisSection R n) (axisProjection R n) :=
    axisProjection_axisSection R n
  exact h.surjective

/-- The polynomial section is injective, since projecting its image recovers
the original polynomial. -/
theorem axisSection_injective : Function.Injective (axisSection R n) := by
  have h : Function.LeftInverse (axisProjection R n) (axisSection R n) :=
    axisProjection_axisSection R n
  exact h.injective

/-- The coordinate images characterize the axis projection among algebra
homomorphisms to the univariate polynomial ring. -/
theorem axisProjection_unique
    (f : (Source R n ⧸ hankelIdeal R n) →ₐ[R] Polynomial R)
    (hX : ∀ i : Fin (n + 1),
      f (Ideal.Quotient.mk (hankelIdeal R n) (MvPolynomial.X i)) =
        if i = 0 then Polynomial.X else 0) : f = axisProjection R n := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  simpa only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] using
    (hX i).trans (axisProjection_X R n i).symm

/-- An algebra map killing all coordinates other than the first is polynomial
evaluation at the image of the first coordinate, composed with the axis
projection. The target need not be commutative. -/
theorem eq_aeval_comp_axisProjection
    {A : Type v} [Semiring A] [Algebra R A]
    (f : (Source R n ⧸ hankelIdeal R n) →ₐ[R] A)
    (hpos : ∀ i : Fin (n + 1), i ≠ 0 →
      f (Ideal.Quotient.mk (hankelIdeal R n) (MvPolynomial.X i)) = 0) :
    f = (Polynomial.aeval
      (f (Ideal.Quotient.mk (hankelIdeal R n)
        (MvPolynomial.X (0 : Fin (n + 1)))))).comp (axisProjection R n) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  by_cases hi : i = 0
  · subst i
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
      axisProjection_X_zero, Polynomial.aeval_X]
  · simpa only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
      axisProjection_X_of_ne_zero R n i hi, map_zero] using hpos i hi

/-- For each element of a semiring algebra, there is a unique algebra map from
the Hankel quotient sending the first coordinate to that element and every
other coordinate to zero. Uniqueness is within these coordinate conditions. -/
theorem existsUnique_axisHom
    {A : Type v} [Semiring A] [Algebra R A] (x : A) :
    ∃! f : (Source R n ⧸ hankelIdeal R n) →ₐ[R] A,
      f (Ideal.Quotient.mk (hankelIdeal R n)
        (MvPolynomial.X (0 : Fin (n + 1)))) = x ∧
      ∀ i : Fin (n + 1), i ≠ 0 →
        f (Ideal.Quotient.mk (hankelIdeal R n) (MvPolynomial.X i)) = 0 := by
  refine ⟨(Polynomial.aeval x).comp (axisProjection R n), ?_, ?_⟩
  · constructor
    · simp only [AlgHom.comp_apply, axisProjection_X_zero, Polynomial.aeval_X]
    · intro i hi
      simp only [AlgHom.comp_apply, axisProjection_X_of_ne_zero R n i hi, map_zero]
  · intro f hf
    simpa only [hf.1] using eq_aeval_comp_axisProjection R n f hf.2

end

/-- In degree zero, the polynomial section is also a left inverse of the axis
projection, since the quotient has only the first coordinate. -/
theorem axisSection_comp_axisProjection_zero :
    (axisSection R 0).comp (axisProjection R 0) =
      AlgHom.id R (Source R 0 ⧸ hankelIdeal R 0) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  have hi : i = (0 : Fin 1) :=
    Fin.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ i.isLt))
  subst i
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
    axisProjection_X_zero, axisSection_X, AlgHom.id_apply]

/-- At degree zero the axis projection is bijective: the Hankel ideal is bottom
and the quotient is the full one-variable polynomial ring. -/
theorem axisProjection_bijective_zero : Function.Bijective (axisProjection R 0) := by
  refine ⟨?_, axisProjection_surjective R 0⟩
  have h : Function.LeftInverse (axisSection R 0) (axisProjection R 0) :=
    fun x => AlgHom.congr_fun (axisSection_comp_axisProjection_zero R) x
  exact h.injective

end ToricIdeals.RationalNormalCurve
