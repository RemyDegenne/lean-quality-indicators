public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set

open scoped ENNReal MeasureTheory

namespace TauCeti

namespace Probability

variable {k l : ℝ}

/-- The `ℝ≥0∞`-valued companion to `chiSquaredPDFReal`. It is a probability density when
`0 < k`. -/
def chiSquaredPDF (k x : ℝ) : ℝ≥0∞ := ENNReal.ofReal (chiSquaredPDFReal k x)

end Probability
end TauCeti
end
end
