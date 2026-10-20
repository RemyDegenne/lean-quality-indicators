namespace P2MW.S_MvPolynomial_logMahlerMeasure_eq_mul_integral_logMahlerMeasure_map_finSuccEquiv

open MeasureTheory Real

namespace MvPolynomial

p2m_open

variable {n : ℕ}

scoped instance : IsFiniteMeasure (circleParamMeasure) := by
  unfold circleParamMeasure; infer_instance

scoped instance : IsFiniteMeasure (torusMeasure n) := by
  unfold torusMeasure; infer_instance

theorem torusMeasure_real_univ : (torusMeasure n).real Set.univ = (2 * π) ^ n := by
  simp [Measure.real, torusMeasure_univ, ENNReal.toReal_pow, ENNReal.toReal_ofReal Real.pi_pos.le]

end MvPolynomial
end P2MW.S_MvPolynomial_logMahlerMeasure_eq_mul_integral_logMahlerMeasure_map_finSuccEquiv
