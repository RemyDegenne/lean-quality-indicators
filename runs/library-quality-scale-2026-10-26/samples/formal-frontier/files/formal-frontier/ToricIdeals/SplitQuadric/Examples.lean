/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ToricIdeals.SplitQuadric.Consequences

/-!
# Coefficients and independent point evaluations on the split quadric

Point evaluations and the coefficient retraction provide elementary boundary
examples independently of the kernel theorem. The range, domain and primality
criteria also specialize to integer, rational and zero-ring coefficients.
Point evaluations are algebraic tests; they do not identify the prime spectrum
with tuples over a field.
-/

@[expose] public section

noncomputable section

universe u

namespace SplitQuadric.Examples

open SplitQuadric

variable (A : Type u) [CommRing A]

/-- The coefficient map has an elementary retraction, independently of the kernel theorem. -/
alias coefficientMap_injective := SplitQuadric.coefficientMap_injective

/-- A point evaluation witnesses a nonzero coordinate for every nontrivial coefficient ring. -/
theorem w_ne_zero [Nontrivial A] : w A ≠ 0 := by
  intro h
  have h' := congrArg (axisPoint A 1) h
  simp at h'

/-- Properness follows from evaluation at a point, without primality or the kernel calculation. -/
theorem relationIdeal_ne_top [Nontrivial A] : relationIdeal A ≠ ⊤ := by
  intro h
  have hzero : quotientMap A (1 : Polynomial A) = 0 := by
    change Ideal.Quotient.mk (relationIdeal A) 1 = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    simp [h]
  have h' := congrArg (axisPoint A 0) hzero
  simp at h'

/-- Coefficient zero divisors persist in the quadric algebra, by the same elementary retraction. -/
theorem coefficient_zero_divisors {a b : A} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a * b = 0) :
    coefficientMap A a ≠ 0 ∧ coefficientMap A b ≠ 0 ∧
      coefficientMap A a * coefficientMap A b = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    exact ha (SplitQuadric.coefficientMap_injective A (by simpa using h))
  · intro h
    exact hb (SplitQuadric.coefficientMap_injective A (by simpa using h))
  · rw [← map_mul, hab, map_zero]

/-- In the zero coefficient ring all coordinate classes coincide with zero. -/
theorem coordinate_eq_zero [Subsingleton A] (i : Fin 4) : coordinate A i = 0 :=
  Subsingleton.elim _ _

end SplitQuadric.Examples
