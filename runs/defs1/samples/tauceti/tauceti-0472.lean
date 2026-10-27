public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

open scoped ENNReal

namespace TauCeti.Probability

variable {s ξ x : ℝ}

/-- The extended nonnegative density of a generalized Pareto law. -/
def generalizedParetoPDF (s ξ x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (generalizedParetoPDFReal s ξ x)

end TauCeti.Probability
end
end
