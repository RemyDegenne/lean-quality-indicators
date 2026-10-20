@[expose] public section

noncomputable section

namespace NavierStokes.ActualStageEstimates

open Set Function Filter ProblemStatement CorrectionState CorrectionStep

open CorrectionInitialization CorrectionInitialization.ActualPrimary

open ActualPhysicalStageBounds

open scoped ContDiff Topology BigOperators

variable {B N0 N : ℕ}

/-- Angular input, given by `actualCycleAngularInput M j hN (R.result j).temporal (R.result
j).rank`. -/
noncomputable def angularInput (R : RunData B N0)
    (M : ActualMeanPhysicalData.InitialCycleInput B N0 N
      (fun _ => ActualCycleParameters.fixedParameters B N0))
    (hN : 4 ≤ N) (j : ℕ) : MeanInput h (CoordinateAlgebra.A h) :=
  actualCycleAngularInput M j hN (R.result j).temporal (R.result j).rank

end NavierStokes.ActualStageEstimates
end
end
