/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Inductions
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Tactic.Ring

/-!
# Polynomial estimates in ultrametric seminormed rings

A uniform coefficient bound controls evaluation, differences of evaluations, and
first-order Taylor remainders on the norm unit ball. Differentiation preserves
the coefficient bound: natural-number multiples do not increase an ultrametric
seminorm. In particular, none of these estimates requires the norm of one to be
one, a separated norm, or completeness.
-/

@[expose] public section

namespace Polynomial

variable {R : Type*}

section SeminormedRing

variable [SeminormedRing R] [IsUltrametricDist R] {f : R[X]} {M : ℝ} {x y : R}

/-- Differentiation preserves a uniform coefficient bound for an ultrametric seminorm. -/
theorem norm_derivative_coeff_le_of_norm_coeff_le
    (hf : ∀ n : ℕ, ‖f.coeff n‖ ≤ M) (n : ℕ) :
    ‖f.derivative.coeff n‖ ≤ M := by
  simpa only [coeff_derivative, nsmul_eq_mul', Nat.cast_add, Nat.cast_one] using
    (IsUltrametricDist.norm_nsmul_le (f.coeff (n + 1)) (n + 1)).trans (hf (n + 1))

/-- On the norm unit ball, evaluation is bounded by any uniform coefficient bound. -/
theorem norm_eval_le_of_norm_coeff_le
    (hf : ∀ n : ℕ, ‖f.coeff n‖ ≤ M) (hx : ‖x‖ ≤ 1) :
    ‖f.eval x‖ ≤ M := by
  induction f using degree_lt_wf.induction with
  | h f ih =>
    by_cases hf0 : f = 0
    · simpa only [hf0, eval_zero, norm_zero, coeff_zero] using hf 0
    have htail : ∀ n : ℕ, ‖f.divX.coeff n‖ ≤ M := fun n => by
      simpa only [coeff_divX] using hf (n + 1)
    have hbound := ih f.divX (degree_divX_lt hf0) htail
    rw [← divX_mul_X_add f, eval_add, eval_mul_X, eval_C]
    apply (IsUltrametricDist.norm_add_le_max _ _).trans
    exact max_le
      ((norm_mul_le _ _).trans
        ((mul_le_of_le_one_right (norm_nonneg _) hx).trans hbound))
      (hf 0)

/-- On the norm unit ball, a polynomial is Lipschitz with any uniform coefficient bound. -/
theorem norm_eval_sub_le_of_norm_coeff_le
    (hf : ∀ n : ℕ, ‖f.coeff n‖ ≤ M) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    ‖f.eval x - f.eval y‖ ≤ M * ‖x - y‖ := by
  induction f using degree_lt_wf.induction with
  | h f ih =>
    by_cases hf0 : f = 0
    · have hM : 0 ≤ M := (norm_nonneg (f.coeff 0)).trans (hf 0)
      simpa only [hf0, eval_zero, sub_self, norm_zero] using
        mul_nonneg hM (norm_nonneg (x - y))
    have htail : ∀ n : ℕ, ‖f.divX.coeff n‖ ≤ M := fun n => by
      simpa only [coeff_divX] using hf (n + 1)
    have hbound := ih f.divX (degree_divX_lt hf0) htail
    have hid : f.eval x - f.eval y =
        (f.divX.eval x - f.divX.eval y) * x + f.divX.eval y * (x - y) := by
      conv_lhs => rw [← divX_mul_X_add f]
      simp only [eval_add, eval_mul_X, eval_C, sub_mul, mul_sub,
        sub_add_sub_cancel, add_sub_add_right_eq_sub]
    rw [hid]
    apply (IsUltrametricDist.norm_add_le_max _ _).trans
    apply max_le
    · exact (norm_mul_le _ _).trans
        ((mul_le_of_le_one_right (norm_nonneg _) hx).trans hbound)
    · exact (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (norm_eval_le_of_norm_coeff_le htail hy)
          (norm_nonneg _))

end SeminormedRing

section SeminormedCommRing

variable [SeminormedCommRing R] [IsUltrametricDist R] {f : R[X]} {M : ℝ} {x y : R}

/-- The first-order Taylor remainder on the norm unit ball has a quadratic bound
with the same uniform coefficient bound, without any characteristic assumption. -/
theorem norm_eval_sub_sub_derivative_mul_le_of_norm_coeff_le
    (hf : ∀ n : ℕ, ‖f.coeff n‖ ≤ M) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    ‖f.eval x - f.eval y - f.derivative.eval y * (x - y)‖ ≤ M * ‖x - y‖ ^ 2 := by
  induction f using degree_lt_wf.induction with
  | h f ih =>
    by_cases hf0 : f = 0
    · have hM : 0 ≤ M := (norm_nonneg (f.coeff 0)).trans (hf 0)
      simpa only [hf0, eval_zero, sub_self, derivative_zero, zero_mul, norm_zero] using
        mul_nonneg hM (sq_nonneg ‖x - y‖)
    have htail : ∀ n : ℕ, ‖f.divX.coeff n‖ ≤ M := fun n => by
      simpa only [coeff_divX] using hf (n + 1)
    have hbound := ih f.divX (degree_divX_lt hf0) htail
    have hderiv : ‖f.divX.derivative.eval y‖ ≤ M :=
      norm_eval_le_of_norm_coeff_le (norm_derivative_coeff_le_of_norm_coeff_le htail) hy
    have hid : f.eval x - f.eval y - f.derivative.eval y * (x - y) =
        x * (f.divX.eval x - f.divX.eval y - f.divX.derivative.eval y * (x - y)) +
          f.divX.derivative.eval y * (x - y) ^ 2 := by
      conv_lhs => rw [← divX_mul_X_add f]
      simp only [eval_add, eval_mul_X, eval_C, derivative_add, derivative_mul,
        derivative_X, derivative_C, mul_one, add_zero]
      ring
    rw [hid]
    apply (IsUltrametricDist.norm_add_le_max _ _).trans
    apply max_le
    · exact (norm_mul_le _ _).trans
        ((mul_le_of_le_one_left (norm_nonneg _) hx).trans hbound)
    · exact (norm_mul_le _ _).trans
        (mul_le_mul hderiv (norm_pow_le' (x - y) (by decide : 0 < 2))
          (norm_nonneg _) ((norm_nonneg (f.coeff 0)).trans (hf 0)))

end SeminormedCommRing

end Polynomial
