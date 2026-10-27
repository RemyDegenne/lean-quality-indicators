public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set

open scoped ENNReal

namespace TauCeti.Probability

/-- The real arcsine density, with value zero outside the open unit interval. -/
def arcsinePDFReal (x : ℝ) : ℝ :=
  if x ∈ Ioo 0 1 then 1 / (π * √(x * (1 - x))) else 0

end TauCeti.Probability
end
end
