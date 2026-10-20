@[expose] public section

noncomputable section

namespace NavierStokes.ActualParticularCycleData

open Set Function Filter WeightedClasses CorrectionState CorrectionStep CorrectionInitialization

open scoped ContDiff Topology BigOperators

section NativeData

variable {B N0 : ℕ} {σ : ℝ} {x : CycleState (Index B N0)}

theorem native_source_class (H : Invariant σ x) (j : ℤ) (hj : j ≠ 0) :
    LabelSumBounds.UniformWaveClass
      (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip
          ActualParticularStageControls.slowStrip))
      ActualParticularStageControls.nativeEnvelope (1/2+σ)
      (ActualParticularStageControls.currentSource (ActualCycleParameters.particularState x) j) :=
  ActualParticularStageControls.current_source_class _ (native_residual H) j hj

end NativeData
end NavierStokes.ActualParticularCycleData
end
end
