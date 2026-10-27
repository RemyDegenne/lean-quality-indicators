@[expose] public section

noncomputable section

namespace NavierStokes.ActualParticularMeanGain

open Set Function Filter WeightedClasses MeanIncrementBounds CorrectionState CorrectionStep

open CorrectionInitialization VariableGaugeMean

open scoped ContDiff Topology BigOperators

/-- Particular velocity: an abbreviation for `(ActualCycleParameters.fixedParameters B
N0).particularVelocity x.coefficients (ActualPrimary.commonContext B) x.state`. -/
noncomputable abbrev particularVelocity {B N0 : ℕ} (x : CycleState (Index B N0)) :=
  (ActualCycleParameters.fixedParameters B N0).particularVelocity x.coefficients
    (ActualPrimary.commonContext B) x.state

end NavierStokes.ActualParticularMeanGain
end
end
