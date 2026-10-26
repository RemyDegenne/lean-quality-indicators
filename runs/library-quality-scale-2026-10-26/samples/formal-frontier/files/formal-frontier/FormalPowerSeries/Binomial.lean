/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.PowerSeries.Binomial
public import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Tactic.Ring

/-!
# Differentiation of binomial power series

The binomial series satisfies `(1 + X) B' = r B` over an algebra of a commutative
binomial ring. This identity does not require a characteristic-zero coefficient algebra.

## Implementation notes

The coefficient identity only uses semiring operations in the coefficient algebra, but
Mathlib's `PowerSeries.derivative` is defined for commutative semirings. Accordingly the
coefficient algebra is assumed to be a commutative semiring, not necessarily a field.

## References

The proof uses Mathlib's formalization of binomial coefficients in
`Mathlib.RingTheory.Binomial` and of binomial power series in
`Mathlib.RingTheory.PowerSeries.Binomial`, in particular `Ring.choose_smul_choose` and
`PowerSeries.binomialSeries_coeff`.
-/

public section

namespace PowerSeries

universe u v

variable {R : Type u} {A : Type v} [CommRing R] [BinomialRing R]
  [CommSemiring A] [Algebra R A]

/-- The binomial series satisfies the differential equation `(1 + X) B' = r B`,
without division by natural numbers or a characteristic-zero assumption on the coefficient
algebra. The coefficient recurrence is obtained from Mathlib's `Ring.choose_smul_choose`. -/
theorem derivative_binomialSeries_mul_one_add_X (r : R) :
    derivative (binomialSeries A r) * (1 + X) =
      C (algebraMap R A r) * binomialSeries A r := by
  have hrec (n : ℕ) :
      Ring.choose r (n + 1) * (n + 1) + Ring.choose r n * n = r * Ring.choose r n := by
    have h := Ring.choose_smul_choose r (Nat.le_succ n)
    simp only [Nat.choose_succ_self_right, Nat.succ_eq_add_one, Nat.add_sub_cancel_left,
      Ring.choose_one_right, nsmul_eq_mul, Nat.cast_add, Nat.cast_one] at h
    calc
      Ring.choose r (n + 1) * (n + 1) + Ring.choose r n * n =
          (n + 1 : R) * Ring.choose r (n + 1) + Ring.choose r n * n := by
        rw [mul_comm (Ring.choose r (n + 1))]
      _ = Ring.choose r n * (r - n) + Ring.choose r n * n := by rw [h]
      _ = r * Ring.choose r n := by ring
  ext n
  rw [mul_add, mul_one, map_add, coeff_C_mul]
  cases n with
  | zero =>
    simp [coeff_derivative, coeff_zero_mul_X, binomialSeries_coeff, Algebra.smul_def]
  | succ n =>
    rw [coeff_succ_mul_X, coeff_derivative, coeff_derivative]
    simp only [binomialSeries_coeff, Algebra.smul_def, mul_one]
    simpa only [map_add, map_mul, map_natCast, map_one, Nat.cast_add, Nat.cast_one] using
      congrArg (algebraMap R A) (hrec (n + 1))

end PowerSeries
