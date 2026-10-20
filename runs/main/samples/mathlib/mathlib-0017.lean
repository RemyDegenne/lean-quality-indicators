public section

namespace EuclideanSpace

open Real MeasureTheory MeasureTheory.Measure ENNReal Metric

@[simp]
lemma volume_closedBall_fin_three (x : EuclideanSpace ℝ (Fin 3)) (r : ℝ) :
    volume (closedBall x r) = .ofReal r ^ 3 * .ofReal (π * 4 / 3) := by
  rw [addHaar_closedBall_eq_addHaar_ball, volume_ball_fin_three x]

end EuclideanSpace
end
