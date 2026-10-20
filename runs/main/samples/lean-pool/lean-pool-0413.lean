@[expose] public section

open MeasureTheory Set Metric

open scoped ENNReal NNReal

open scoped ComplexConjugate

namespace QuadraticCarleson

theorem lintegral_selectedAverageKernel_mul {N : ℕ} (r : Fin N → ℝ)
    (σ : ℝ → Fin N) {f : ℝ → ℝ≥0∞} (hf : Measurable f) (x : ℝ) :
    (∫⁻ y, selectedAverageKernel r σ x y * f y) = centeredAverage (r (σ x)) f x := by
  unfold selectedAverageKernel centeredAverage
  have hid (y : ℝ) :
      (closedBall x (r (σ x))).indicator (fun _ ↦ (ENNReal.ofReal (2 * r (σ x)))⁻¹) y * f y =
      (closedBall x (r (σ x))).indicator
        (fun y ↦ (ENNReal.ofReal (2 * r (σ x)))⁻¹ * f y) y := by
    by_cases hy : y ∈ closedBall x (r (σ x)) <;> simp [Set.indicator, hy]
  simp_rw [hid]
  rw [lintegral_indicator measurableSet_closedBall,
    lintegral_const_mul _ hf]
  rw [div_eq_mul_inv, mul_comm]

end QuadraticCarleson
end
