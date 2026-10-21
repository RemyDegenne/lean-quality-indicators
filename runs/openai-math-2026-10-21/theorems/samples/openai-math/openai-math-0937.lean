namespace OAI

noncomputable section

open MeasureTheory

open scoped ENNReal

namespace Problem358.MomentCouplingBounds

variable {A F : Type*} [MeasurableSpace A] {μ : Measure A}
  [IsProbabilityMeasure μ] [NormedAddCommGroup F]

theorem integral_norm_le_sqrt_integral_sq_norm {f : A → F} (hf : MemLp f 2 μ) :
    (∫ x, ‖f x‖ ∂μ) ≤ Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂μ) := by
  apply Real.le_sqrt_of_sq_le
  have h := ProbabilityTheory.variance_nonneg (fun x => ‖f x‖) μ
  rw [ProbabilityTheory.variance_eq_sub hf.norm] at h
  exact sub_nonneg.mp h

end Problem358.MomentCouplingBounds
end
end OAI
