@[expose] public section

noncomputable section

namespace NavierStokes.ActualCurrentParticularPhysical

open Set Function Filter ProblemStatement HarmonicCalculus

open CorrectionState CorrectionStep CorrectionInitialization

open scoped Topology ContDiff BigOperators

variable {B N0 : ℕ}

theorem nativeCurl_reindex (x : CycleState (Label B N0)) (l : Label B N0)
    (j : ℤ) (n : ℕ) (z : PhysicalResidualBridge.Cylinder) :
    CurlClassBounds.cylindricalCurl PhysicalResidualBridge.ScaledGraph.radius
      (PhysicalResidualBridge.commonGraph (ChartScales.Q n) CorrectionInitialization.ActualPrimary.h
        (CommonWindow.index CorrectionInitialization.ActualPrimary.h n)).radial
      PhysicalResidualBridge.ScaledGraph.angular
      (PhysicalResidualBridge.commonGraph (ChartScales.Q n) CorrectionInitialization.ActualPrimary.h
        (CommonWindow.index CorrectionInitialization.ActualPrimary.h n)).axial
      (fun y => nativePotential x l j n (PhysicalParticularWave.waveEquiv y)) z =
    CurlClassBounds.cylindricalCurl ((copyData x l j).background.radius n)
      ((ActualParticularStageControls.directions (B := B)).radialField n)
      (fun _ => (ActualParticularStageControls.directions (B := B)).angular)
      ((ActualParticularStageControls.directions (B := B)).axialField
        (ParticularParameters.nativeStrip ActualParticularStageControls.associatedStrip) n)
      (nativePotential x l j n) (PhysicalParticularWave.waveEquiv z) := by
  have he := ActualParticularRealization.curl_pull PhysicalParticularWave.waveEquiv
    ((ActualParticularStageControls.assembly x l).background.radius n)
    ((ActualParticularStageControls.assembly x l).directions.radialField n)
    (fun _ => (ActualParticularStageControls.assembly x l).directions.angular)
    ((ActualParticularStageControls.assembly x l).directions.axialField
      (ParticularParameters.nativeStrip ActualParticularStageControls.associatedStrip) n)
    (nativePotential x l j n)
  rw [(ActualParticularCoherence.targetChart x l n).radius,
    (ActualParticularCoherence.targetChart x l n).radial,
    (ActualParticularCoherence.targetChart x l n).angular,
    (ActualParticularCoherence.targetChart x l n).axial] at he
  exact congrFun he z

end NavierStokes.ActualCurrentParticularPhysical
end
end
