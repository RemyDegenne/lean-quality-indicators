public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set

open scoped ENNReal

namespace TauCeti.Probability

variable {m s x : ℝ}

/-- The real-valued density of the Gumbel law with location `m` and scale `s`.

For nonpositive scale it is zero, matching the totalized measure. -/
def gumbelPDFReal (m s x : ℝ) : ℝ :=
  if 0 < s then
    Real.exp (-((x - m) / s)) * Real.exp (-Real.exp (-((x - m) / s))) / s
  else 0

end TauCeti.Probability
end
end
