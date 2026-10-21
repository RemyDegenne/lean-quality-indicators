namespace OAI

noncomputable section

open MeasureTheory Set

open scoped Interval

namespace InternalCatalan

theorem integral_oddPrimeLoss_25_65 :
    (∫ x in (25 : ℝ)..65, oddPrimeLoss x) = 3809 / 2 := by
  have h := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (continuous_oddPrimeLoss.intervalIntegrable 0 25)
    (continuous_oddPrimeLoss.intervalIntegrable 25 65)
  rw [integral_oddPrimeLoss_0_25, integral_oddPrimeLoss] at h
  linarith

end InternalCatalan
end
end OAI
