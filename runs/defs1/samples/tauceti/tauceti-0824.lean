public section

noncomputable section

open MeasureTheory Set Metric Filter

namespace TauCeti.Green.Examples

/-- An open field domain around the two boundary components which excludes the central hole. -/
def annulusDomain (r R : ℝ) : Set ℂ := {z | r / 2 < ‖z‖ ∧ ‖z‖ < R + 1}

end TauCeti.Green.Examples
end
end
