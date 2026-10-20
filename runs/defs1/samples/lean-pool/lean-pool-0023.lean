@[expose] public section

noncomputable section

namespace NavierStokes.ActualInitialization

open Set Function Filter CorrectionState CorrectionInitialization

open scoped ContDiff Topology BigOperators

variable {B N0 : ℕ}

/-- Coefficients, bundling `labels`, `blocks`, `gaussian`, `aliasCoefficients` and the required
compatibility proofs. -/
noncomputable def coefficients (B N0 : ℕ) : CorrectionStep.CycleCoefficients (Index B N0) where
  labels := ActualPrimary.activeLabels ActualPrimary.standardRegion B N0
  blocks := primaryBlock
  gaussian l := (gaussianBlock l).velocity
  aliasCoefficients _ := 0
  residualBand := 2

end NavierStokes.ActualInitialization
end
end
