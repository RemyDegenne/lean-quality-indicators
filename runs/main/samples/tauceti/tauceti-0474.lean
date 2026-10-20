public section

noncomputable section

open MeasureTheory Set Metric

namespace TauCeti.Green.Examples

theorem circulationFun_area_circleMap (R t : ℝ) :
    circulationFun areaP areaQ (circleMap 0 R) t = R ^ 2 / 2 := by
  rw [circulationFun, deriv_circleMap, areaP, areaQ]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, circleMap_zero_re, circleMap_zero_im]
  nlinarith [Real.sin_sq_add_cos_sq t]

end TauCeti.Green.Examples
end
end
