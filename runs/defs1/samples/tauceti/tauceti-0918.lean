public section

noncomputable section

open MeasureTheory Set Metric

namespace TauCeti.Green.Examples

/-- The diagonal real linear map describing the ellipse axes. -/
def ellipseLinearMap (a b : ℝ) : ℂ →ₗ[ℝ] ℂ :=
  Complex.basisOneI.constr ℝ ![(a : ℂ), (b : ℂ) * Complex.I]

end TauCeti.Green.Examples
end
end
