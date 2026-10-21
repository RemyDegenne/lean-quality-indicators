namespace OAI

universe uE

section KernelBalls

open MeasureTheory Set Metric

open scoped ENNReal

noncomputable section

namespace HenonLaneEmden.WeakPDE

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma integrable_shifted_power_ball (hn : 1 ≤ Module.finrank ℝ E) {a : ℝ}
    (ha : -(Module.finrank ℝ E:ℝ) < a) (r : ℝ) (x : E) :
    Integrable ((ball x r).indicator (fun y => ‖x-y‖^a)) := by
  have hi : IntegrableOn (fun z : E => ‖z‖^a) (ball 0 r) :=
    ((locallyIntegrable_norm_power hn a ha).integrableOn_isCompact (isCompact_closedBall 0 r)).mono_set ball_subset_closedBall
  have hI := hi.integrable_indicator measurableSet_ball
  simpa only [Function.comp_def,← shifted_ball_indicator] using
    (Measure.measurePreserving_sub_left volume x).integrable_comp hI.aestronglyMeasurable |>.mpr hI

end HenonLaneEmden.WeakPDE
end
end KernelBalls
end OAI
