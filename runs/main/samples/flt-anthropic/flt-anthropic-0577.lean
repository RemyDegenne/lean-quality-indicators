namespace P2MW.S_MvPolynomial_ae_restrict_torusBox_eval_circleMap_ne_zero

open MeasureTheory Real

namespace MvPolynomial

p2m_open

variable {n : ℕ}

scoped instance : IsFiniteMeasure (circleParamMeasure) := by
  unfold circleParamMeasure; infer_instance

scoped instance : IsFiniteMeasure (torusMeasure n) := by
  unfold torusMeasure; infer_instance

theorem logMahlerMeasure_eq_mul_integral_torusMeasure (P : MvPolynomial (Fin n) ℂ) :
    P.logMahlerMeasure =
      ((2 * π)⁻¹) ^ n * ∫ θ, Real.log ‖eval (fun i ↦ circleMap 0 1 (θ i)) P‖ ∂(torusMeasure n) := by
  rw [logMahlerMeasure, volume_restrict_torusBox]

end MvPolynomial
end P2MW.S_MvPolynomial_ae_restrict_torusBox_eval_circleMap_ne_zero
