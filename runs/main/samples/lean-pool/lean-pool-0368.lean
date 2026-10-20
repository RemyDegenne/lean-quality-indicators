@[expose] public section

noncomputable section

namespace NavierStokes.ActualCycleResidualBounds

open Set Function Filter WeightedClasses CorrectionState CorrectionStep CorrectionInitialization

open LocalPhysicalCopyBounds PhysicalResidualJetBounds LabelSumBounds

open PhysicalWaveSum PhysicalGraphBounds

open scoped Topology ContDiff BigOperators

namespace Invariant

variable {B N0 : ℕ} {σ : ℝ} {x : CycleState (Index B N0)} (H : Invariant σ x)

include H

theorem source_sum_native (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) :
    NativeBounds 4 (HarmonicResidual.liftDomain ActualInitialization.geometry.strip.domain)
      (ActualPrimary.h * (1/2 + σ)) (fun m => (2 * ActualPrimary.h) * m)
      (fun (_ : Unit) n z => ∑ l ∈ x.coefficients.labels n, (source x l).oscillation n z) :=
  block_window_sum hN x.coefficients.labels (source x) H.source_coeff_zero_off
      (H.source_oscillation_native hN)

end Invariant
end NavierStokes.ActualCycleResidualBounds
end
end
