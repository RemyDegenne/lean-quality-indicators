@[expose] public section

noncomputable section

namespace NavierStokes.ActualInitialization

open Set Function Filter CorrectionState CorrectionInitialization

open scoped ContDiff Topology BigOperators

variable {B N0 : ℕ}

/-- Rank state, constructed using `VariableGaugeMean.rankStageState`. -/
noncomputable def rankState (B N0 : ℕ) : State Point :=
  VariableGaugeMean.rankStageState ActualPrimary.commonGauge ActualPrimary.rankData axial
    (ActualPrimary.commonContext B) (temporalState B N0)

end NavierStokes.ActualInitialization
end
end
