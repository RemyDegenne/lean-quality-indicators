public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace TauCeti.Probability

@[simp]
theorem support_arcsineMeasure : arcsineMeasure.support = Icc 0 1 := by
  simpa only [arcsineMeasure] using
    support_betaMeasure (show (0 : ℝ) < 1 / 2 by norm_num)
      (show (0 : ℝ) < 1 / 2 by norm_num)

end TauCeti.Probability
end
end
