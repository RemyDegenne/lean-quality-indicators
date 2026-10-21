namespace OAI

noncomputable section

namespace DepthThreeLowerBound

theorem independenceOrder_add_two_mul_hashDimension_le (d : ℕ) (hd : 4096 ≤ d) :
    (independenceOrder d + 2) * hashDimension d ≤ 3 * d := by
  have hdreal : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (by omega : 1 ≤ d)
  have hdpos : (0 : ℝ) < (d : ℝ) := lt_of_lt_of_le zero_lt_one hdreal
  have ht := independenceOrder_rpow_le d
  have hr := hashDimension_rpow_upper d (by omega)
  have hfour := four_le_rpow_one_sixth d hd
  have hy : 0 ≤ (d : ℝ) ^ (2 / 3 : ℝ) :=
    Real.rpow_nonneg (Nat.cast_nonneg d) _
  have hproduct : ((independenceOrder d : ℝ) + 2) * (hashDimension d : ℝ) ≤
      ((d : ℝ) ^ (1 / 6 : ℝ) + 2) * (2 * (d : ℝ) ^ (2 / 3 : ℝ)) :=
    mul_le_mul (by linarith) hr
      (Nat.cast_nonneg (hashDimension d)) (by linarith)
  have hslack : 0 ≤ ((d : ℝ) ^ (1 / 6 : ℝ) - 4) *
      ((d : ℝ) ^ (2 / 3 : ℝ)) :=
    mul_nonneg (by linarith) hy
  have hsum : (d : ℝ) ^ (1 / 6 : ℝ) * (d : ℝ) ^ (2 / 3 : ℝ) =
      (d : ℝ) ^ (5 / 6 : ℝ) := by
    rw [← Real.rpow_add hdpos]
    norm_num
  have hlast : (d : ℝ) ^ (5 / 6 : ℝ) ≤ (d : ℝ) := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le hdreal (by norm_num : (5 / 6 : ℝ) ≤ 1))
  have hreal : ((independenceOrder d : ℝ) + 2) * (hashDimension d : ℝ) ≤
      3 * (d : ℝ) := by
    nlinarith [hproduct, hslack, hsum, hlast]
  exact_mod_cast hreal

end DepthThreeLowerBound
end
end OAI
