@[expose] public noncomputable section

open MeasureTheory

open scoped MeasureTheory

namespace AleksandrovDifferentiability

variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

variable [MeasurableSpace E]

theorem secondOrderDifferentiableAE_iff_measure_secondOrderBadSet_eq_zero
    {μ : Measure E} {u : E → ℝ} :
    SecondOrderDifferentiableAE μ u ↔ μ (secondOrderBadSet u) = 0 := by
  rw [SecondOrderDifferentiableAE, ae_iff]
  have hset : {x | ¬ SecondOrderDifferentiableAt u x} = secondOrderBadSet u := by
    ext x
    rfl
  rw [hset]

end AleksandrovDifferentiability
end
