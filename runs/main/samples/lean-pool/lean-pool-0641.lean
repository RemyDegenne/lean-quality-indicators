public section

open Complex Filter Function MeasureTheory Metric Set

open scoped ENNReal NNReal Real Topology

namespace SeveralComplexVariables

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem isCompleteReinhardt_closedPolydisc {ι : Type*} (r : ι → ℝ) :
    IsCompleteReinhardt (closedPolydisc (0 : ι → ℂ) r) := by
  intro z hz w hw
  simp only [mem_closedPolydisc, Pi.zero_apply, dist_zero_right] at hz ⊢
  exact fun i => (hw i).trans (hz i)

end SeveralComplexVariables
end
