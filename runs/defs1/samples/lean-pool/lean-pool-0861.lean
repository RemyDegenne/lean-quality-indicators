@[expose] public section

namespace NavierStokes.ActualInitialCoherence

noncomputable section

open Set Function Filter

open scoped ContDiff Topology BigOperators

open CorrectionState MeanIncrementBounds MeanStateRegularity PhysicalResidualNaturality

section IndividualBlocks

open CorrectionInitialization CorrectionInitialization.ActualPrimary GaugeStateCoherence

variable {B N0 : ℕ}

/-- Phase, given by `(pieces B N0 l).coefficients.phase n (x, 0)`. -/
noncomputable def phase (l : Label B N0 × Fin 2) (n : ℕ) (x : Point) : ℝ :=
  (pieces B N0 l).coefficients.phase n (x, 0)

end IndividualBlocks
end
end NavierStokes.ActualInitialCoherence
end
