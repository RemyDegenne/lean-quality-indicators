public section

namespace PowerSeries

universe u v

variable {R : Type u} {A : Type v} [CommRing R] [BinomialRing R]
  [CommSemiring A] [Algebra R A]

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
end
