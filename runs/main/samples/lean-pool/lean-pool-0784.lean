@[expose] public section

open scoped Nat

open BigOperators Finset

variable {R : Type*}

namespace Polynomial

lemma shiftedLegendre_poly_eval_zero_eq_zero {m : ℕ} (h : m < n) :
    eval 0 ((⇑derivative)^[m] (X ^ n * (1 - X) ^ n) : ℝ[X]) = 0 := by
  rw [Polynomial.iterate_derivative_mul, Polynomial.eval_finsetSum]
  apply Finset.sum_eq_zero
  intro x hx
  simp_all only [Nat.succ_eq_add_one, Finset.mem_range, nsmul_eq_mul, eval_mul, eval_natCast,
    mul_eq_zero, Nat.cast_eq_zero]
  right; left
  simp only [Polynomial.iterate_derivative_X_pow_eq_smul, eval_smul, eval_pow, eval_X,
    smul_eq_mul, mul_eq_zero, Nat.cast_eq_zero, Nat.descFactorial_eq_zero_iff_lt,
    pow_eq_zero_iff', ne_eq, true_and]
  right
  suffices n - (m - x) > 0 by linarith
  simp only [gt_iff_lt, tsub_pos_iff_lt]
  rw [Nat.lt_add_one_iff] at hx
  calc
    m - x ≤ m := by simp
    _ < n := by exact h

end Polynomial
end
