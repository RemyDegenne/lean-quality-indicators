@[expose] public section

noncomputable section

open Set Filter Function

open scoped Topology ContDiff BigOperators

namespace NavierStokes.PhysicalCoordinateBounds

open SimilarityCoordinates

theorem xLift_homogeneous (a : ℝ) {r : ℝ} (hr : 0 < r)
    {y : Point} (_hy : y ∈ positiveTime) :
    xLift (dilation a r y) = r ^ (0 : ℝ) * xLift y := by
  dsimp only [xLift, dilation_apply]
  rw [Real.rpow_zero, one_mul]
  exact mul_div_mul_left _ _ hr.ne'

end NavierStokes.PhysicalCoordinateBounds
end
end
