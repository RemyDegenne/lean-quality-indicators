namespace P2MW.S_Real_norm_le_and_norm_integral_cexp_mul_le_mul_inv_one_add_abs_sq_of_piecewise_contDiff_two

set_option autoImplicit false

open MeasureTheory Real

namespace R4WinKink

theorem ibp_once (u : ℝ → ℂ) (hu : Differentiable ℝ u) (hu' : Continuous (deriv u))
    (c : ℂ) (hc : c ≠ 0) (a b : ℝ) :
    ∫ x in a..b, u x * Complex.exp (c * x) =
      (u b * Complex.exp (c * b) - u a * Complex.exp (c * a)) / c
        - c⁻¹ * ∫ x in a..b, deriv u x * Complex.exp (c * x) := by
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := u) (v := fun y : ℝ => Complex.exp (c * y) / c) (u' := deriv u)
    (v' := fun y : ℝ => Complex.exp (c * y)) (a := a) (b := b)
    (fun x _ => (hu x).hasDerivAt) (fun x _ => hasDerivAt_exp_div c hc x)
    (hu'.intervalIntegrable _ _) ((continuous_exp_cst c).intervalIntegrable _ _)
  rw [h]
  have h2 : ∫ x in a..b, deriv u x * (Complex.exp (c * x) / c) =
      c⁻¹ * ∫ x in a..b, deriv u x * Complex.exp (c * x) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    ext x
    field_simp
  rw [h2]
  field_simp

end R4WinKink
end P2MW.S_Real_norm_le_and_norm_integral_cexp_mul_le_mul_inv_one_add_abs_sq_of_piecewise_contDiff_two
