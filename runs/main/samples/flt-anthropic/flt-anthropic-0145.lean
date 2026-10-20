namespace P2MW.S_MeasureTheory_integral_normSq_det_div_mul_comp_moebius_complex

set_option autoImplicit false

open MeasureTheory

noncomputable section

namespace ARCHA3C

theorem det_D (l : ℂ) : (D l).det = ‖l‖ ^ 2 := by
  simp [D, ContinuousLinearMap.det, LinearMap.det_restrictScalars, Algebra.norm_complex_eq, Complex.normSq_eq_norm_sq]

end ARCHA3C
end
end P2MW.S_MeasureTheory_integral_normSq_det_div_mul_comp_moebius_complex
