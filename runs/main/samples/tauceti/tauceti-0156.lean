public section

noncomputable section

namespace TauCeti

open Complex Filter MeasureTheory Set Topology UpperHalfPlane

variable {ι : Type*} [Fintype ι]

theorem schwarzChristoffelEdgeAngle_eq_pi_mul_sum_of_forall_lt (a e : ι → ℝ) {c : ℝ}
    (hc : ∀ i, c < a i) :
    schwarzChristoffelEdgeAngle a e c = Real.pi * ∑ i, e i := by
  rw [schwarzChristoffelEdgeAngle_eq_sum_filter]
  simp only [hc, Finset.filter_true]

end TauCeti
end
end
