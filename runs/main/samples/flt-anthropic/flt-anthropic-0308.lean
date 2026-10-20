namespace P2MW.S_LanglandsTunnell_setIntegral_setIntegral_cpow_mul_pow_mul_exp_mul_gaussianAverage_eq_Gamma_mul_exp_mul_eval_of_isHomogeneous

set_option autoImplicit false

open MeasureTheory Set Real Complex

namespace FiberAsm

theorem integrable_moment (x : ℝ) (n : ℕ) : Integrable (fun z : ℝ => ((x : ℂ) - I * (z : ℂ)) ^ n * gz z) := by
  have hmaj := (((integrable_abs_pow_mul_exp 0).const_mul (2 ^ n * |x| ^ n)).add
    ((integrable_abs_pow_mul_exp n).const_mul ((2 : ℝ) ^ n)))
  refine Integrable.mono' hmaj (by unfold gz; exact Continuous.aestronglyMeasurable (by fun_prop)) (ae_of_all _ fun z => ?_)
  rw [norm_mul, norm_pow, gz, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have h1 : ‖(x : ℂ) - I * (z : ℂ)‖ ≤ |x| + |z| := by
    calc ‖(x : ℂ) - I * (z : ℂ)‖ ≤ ‖(x : ℂ)‖ + ‖I * (z : ℂ)‖ := norm_sub_le _ _
      _ = |x| + |z| := by rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  have h2 : ‖(x : ℂ) - I * (z : ℂ)‖ ^ n ≤ 2 ^ n * (|x| ^ n + |z| ^ n) :=
    (pow_le_pow_left₀ (norm_nonneg _) h1 n).trans (add_pow_le _ _ (abs_nonneg _) (abs_nonneg _) n)
  simp only [Pi.add_apply, pow_zero, one_mul]
  have := Real.exp_pos (-(Real.pi * z ^ 2))
  nlinarith [h2, pow_nonneg (abs_nonneg z) n, pow_nonneg (abs_nonneg x) n]

end FiberAsm
end P2MW.S_LanglandsTunnell_setIntegral_setIntegral_cpow_mul_pow_mul_exp_mul_gaussianAverage_eq_Gamma_mul_exp_mul_eval_of_isHomogeneous
