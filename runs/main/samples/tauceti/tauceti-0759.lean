public section

open PowerSeries ArithmeticFunction

open scoped ArithmeticFunction.sigma LaurentSeries

namespace TauCeti

@[simp]
theorem constantCoeff_tateCurve_a₆ : constantCoeff tateCurve.a₆ = 0 := by
  have h := twelve_mul_coeff_tateCurve_a₆ 0
  simp only [ArithmeticFunction.map_zero, coeff_zero_eq_constantCoeff_apply] at h
  omega

end TauCeti
end
