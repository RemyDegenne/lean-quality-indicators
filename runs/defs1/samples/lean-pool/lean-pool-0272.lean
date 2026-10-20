@[expose] public section

noncomputable section

namespace NavierStokes.ActivationStocks

open Set Filter ProfileHistories StressActivation

open scoped Topology ContDiff

namespace FromReference

open ReferencePath

variable (N : ReferencePath.Input)

/-- Initial, defined pointwise by `profileHistory (N.histories hδ hδT P0 hP0) r (N.endpoint,
η)`. -/
noncomputable def initial {δ : ℝ} (hδ : 0 < δ) (hδT : 2 * δ < rampLimit)
    (P0 : ℝ → ℝ) (hP0 : ContDiff ℝ ∞ P0) : HistoryRow → ℝ → ℝ :=
  fun r η => profileHistory (N.histories hδ hδT P0 hP0) r (N.endpoint, η)

end FromReference
end NavierStokes.ActivationStocks
end
end
