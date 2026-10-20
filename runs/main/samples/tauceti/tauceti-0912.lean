public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set Function Topology

namespace MeasureTheory.Measure

variable {t x : ℝ}

theorem nonempty_setOf_lt_cdf (μ : Measure ℝ) (ht : t < 1) : {x : ℝ | t < cdf μ x}.Nonempty :=
  ((tendsto_cdf_atTop μ).eventually (eventually_gt_nhds ht)).exists

end MeasureTheory.Measure
end
end
