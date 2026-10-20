@[expose] public section

noncomputable section

namespace NavierStokes.ActualCycleCoherence

open Set Function Filter CorrectionState CorrectionStep

open PhysicalResidualNaturality GaugeStateCoherence

open CorrectionInitialization CorrectionInitialization.ActualPrimary

open scoped ContDiff Topology BigOperators

theorem Coherent.particular_blocks {B N0 : ℕ} {x : CycleState (Index B N0)} (H : Coherent x) :
    BlocksCoherent (ActualCycleParameters.particularState x).coefficients :=
  H.blocks.reindex (ActualCycleParameters.swap B N0).symm

end NavierStokes.ActualCycleCoherence
end
end
