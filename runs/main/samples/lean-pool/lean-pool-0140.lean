@[expose] public section

noncomputable section

notation ρ "[" idx " ↦ " x "]" => updateVar ρ idx x

section

@[expose] public section

namespace LeanCert.Core

namespace IntervalReal

theorem abs_arsinh_le_abs (x : ℝ) : |Real.arsinh x| ≤ |x| := by
  rcases le_or_gt 0 x with hx | hx
  · -- Case x ≥ 0: arsinh x ≥ 0 by monotonicity of arsinh
    rcases eq_or_lt_of_le hx with rfl | hx_pos
    · -- x = 0
      simp [Real.arsinh_zero]
    · -- x > 0
      have harsinh_nonneg : 0 ≤ Real.arsinh x := Real.arsinh_nonneg_iff.mpr (le_of_lt hx_pos)
      have hcont : ContinuousOn Real.arsinh (Set.Icc 0 x) :=
        Real.continuous_arsinh.continuousOn
      have hdiff : DifferentiableOn ℝ Real.arsinh (Set.Ioo 0 x) :=
        Real.differentiable_arsinh.differentiableOn
      obtain ⟨c, ⟨_, _⟩, hc_eq⟩ := exists_deriv_eq_slope Real.arsinh hx_pos hcont hdiff
      simp only [Real.arsinh_zero, sub_zero] at hc_eq
      have hderiv_bound : |deriv Real.arsinh c| ≤ 1 := arsinh_deriv_abs_le_one c
      rw [abs_of_nonneg harsinh_nonneg, abs_of_pos hx_pos]
      have heq : Real.arsinh x = deriv Real.arsinh c * x := by rw [hc_eq]; field_simp
      calc Real.arsinh x = deriv Real.arsinh c * x := heq
        _ ≤ |deriv Real.arsinh c * x| := le_abs_self _
        _ = |deriv Real.arsinh c| * |x| := abs_mul _ _
        _ ≤ 1 * x := by rw [abs_of_pos hx_pos]; nlinarith [abs_nonneg x, hderiv_bound]
        _ = x := one_mul _
  · -- Case x < 0: use oddness arsinh(-x) = -arsinh(x)
    have hx_neg : -x > 0 := by linarith
    -- For x < 0, arsinh x < 0 (arsinh is strictly increasing, arsinh 0 = 0)
    have harsinh_neg : Real.arsinh x < 0 := Real.arsinh_neg_iff.mpr hx
    have harsinh_neg_nonneg : 0 ≤ Real.arsinh (-x) := Real.arsinh_nonneg_iff.mpr (by linarith)
    -- Use the positive case on -x
    have hcont : ContinuousOn Real.arsinh (Set.Icc 0 (-x)) :=
      Real.continuous_arsinh.continuousOn
    have hdiff : DifferentiableOn ℝ Real.arsinh (Set.Ioo 0 (-x)) :=
      Real.differentiable_arsinh.differentiableOn
    obtain ⟨c, ⟨_, _⟩, hc_eq⟩ := exists_deriv_eq_slope Real.arsinh hx_neg hcont hdiff
    simp only [Real.arsinh_zero, sub_zero] at hc_eq
    have hderiv_bound : |deriv Real.arsinh c| ≤ 1 := arsinh_deriv_abs_le_one c
    rw [abs_of_neg harsinh_neg, abs_of_neg hx]
    have heq : Real.arsinh (-x) = deriv Real.arsinh c * (-x) := by
      have hne : (-x) ≠ 0 := ne_of_gt hx_neg
      have : deriv Real.arsinh c * (-x) = (Real.arsinh (-x) / (-x)) * (-x) := by rw [hc_eq]
      rw [this, div_mul_cancel₀ _ hne]
    calc -Real.arsinh x = Real.arsinh (-x) := by rw [Real.arsinh_neg]
      _ = deriv Real.arsinh c * (-x) := heq
      _ ≤ |deriv Real.arsinh c * (-x)| := le_abs_self _
      _ = |deriv Real.arsinh c| * |-x| := abs_mul _ _
      _ ≤ 1 * (-x) := by rw [abs_of_pos hx_neg]; nlinarith [abs_nonneg (-x), hderiv_bound]
      _ = -x := one_mul _

end IntervalReal
end LeanCert.Core
end
end
end
end
