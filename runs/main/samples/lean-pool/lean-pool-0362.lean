@[expose] public section

open Function MeasureTheory Metric Set

open scoped ENNReal NNReal

namespace QuadraticCarleson

theorem cutoffBoundaryKernel_norm_le
    (lam : ℝ) {ρ t : ℝ} (hρ : 0 < ρ) :
    ‖cutoffBoundaryKernel lam ρ t‖ ≤ 1 / ρ := by
  by_cases hin : |t| ≤ ρ
  · rw [cutoffBoundaryKernel_eq_zero_of_abs_le lam hρ hin]
    simpa using one_div_nonneg.mpr hρ.le
  · by_cases hout : 2 * ρ ≤ |t|
    · rw [cutoffBoundaryKernel_eq_zero_of_two_mul_le_abs lam hρ hout]
      simpa using one_div_nonneg.mpr hρ.le
    · have ht0 : t ≠ 0 := by
        intro h
        apply hin
        simp [h, hρ.le]
      have hρt : ρ < |t| := lt_of_not_ge hin
      rw [cutoffBoundaryKernel, ite_eq_right ht0, ite_eq_right hin, norm_mul, norm_phase,
        mul_one, Complex.norm_real, Real.norm_eq_abs, abs_div]
      simp only [sub_zero]
      rw [abs_of_nonneg (dyadicCutoff_nonneg _)]
      calc
        dyadicCutoff (t / (4 * ρ)) / |t| ≤ 1 / |t| :=
          div_le_div_of_nonneg_right (dyadicCutoff_le_one _) (abs_nonneg _)
        _ ≤ 1 / ρ := one_div_le_one_div_of_le hρ hρt.le

end QuadraticCarleson
end
