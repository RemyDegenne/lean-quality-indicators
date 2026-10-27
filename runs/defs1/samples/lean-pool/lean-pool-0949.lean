@[expose] public section

noncomputable section

open Set Function Filter MeasureTheory

open scoped ContDiff Topology BigOperators

namespace NavierStokes.SlowStressSupport

/-- Smooth: an abbreviation for `ContDiffOn ℝ ∞ f (region S)`. -/
abbrev Smooth (S : Set ℝ) (f : Field) := ContDiffOn ℝ ∞ f (region S)

end NavierStokes.SlowStressSupport
end
end
