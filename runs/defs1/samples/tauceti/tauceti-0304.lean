public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set

open scoped ENNReal

namespace TauCeti.Probability

variable {η b x : ℝ}

/-- The real Gompertz density, zero outside positive parameters and positive arguments. -/
def gompertzPDFReal (η b x : ℝ) : ℝ :=
  if 0 < η ∧ 0 < b ∧ 0 < x then
    η * b * exp (b * x) * exp (-η * (exp (b * x) - 1)) else 0

end TauCeti.Probability
end
end
