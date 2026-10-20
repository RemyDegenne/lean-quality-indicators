@[expose] public section

open Set

open scoped ENNReal InnerProductSpace NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem norm_le_numericalRadius_of_mem_closure_numericalRange
    (A : E →L[ℂ] E) {z : ℂ} (hz : z ∈ closure (numericalRange A)) :
    ‖z‖ ≤ numericalRadius A := by
  have hz' := closure_numericalRange_subset_closedBall_numericalRadius A hz
  simpa only [Metric.mem_closedBall, dist_zero_right] using hz'

end
