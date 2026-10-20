@[expose] public section

noncomputable section

namespace NavierStokes.ActualCycleParameters

open Set Function CorrectionState CorrectionStep CorrectionInitialization

open scoped BigOperators

/-- Particular state, given by `reindexState (swap B N0).symm x`. -/
noncomputable def particularState {B N0 : ℕ} (x : CycleState (Index B N0)) :
    CycleState (ParticularIndex B N0) := reindexState (swap B N0).symm x

end NavierStokes.ActualCycleParameters
end
end
