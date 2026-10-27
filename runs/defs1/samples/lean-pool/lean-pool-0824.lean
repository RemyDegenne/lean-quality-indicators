@[expose] public section

namespace NavierStokes.ActualInitialCoherence

noncomputable section

open Set Function Filter

open scoped ContDiff Topology BigOperators

open CorrectionState MeanIncrementBounds MeanStateRegularity PhysicalResidualNaturality

section IndividualBlocks

open CorrectionInitialization CorrectionInitialization.ActualPrimary GaugeStateCoherence

variable {B N0 : ℕ}

/-- Gaussian block, given by `(pieces B N0 l).excludedBlock (phase l) (angularMode l)`. -/
noncomputable def gaussianBlock (l : Label B N0 × Fin 2) : HarmonicBlock Point :=
  (pieces B N0 l).excludedBlock (phase l) (angularMode l)

end IndividualBlocks
end
end NavierStokes.ActualInitialCoherence
end
