@[expose] public section

noncomputable section

namespace NavierStokes.ActualWaveRegularityData

open Set Function Filter WeightedClasses HarmonicCalculus

open CorrectionInitialization CommonCoverSolve TorusInverse

open scoped Topology ContDiff BigOperators

variable {B N0 : ℕ}

theorem strip_zeta (x : FullPoint) : ActualSignedStageControls.fullStrip.zeta x =
    WaveEdgeExtension.flatWeight radius (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
      (PrimaryTargetBounds.rightRadius ActualPrimary.nominal)
      (FinalSlowBase.edgeExponent ActualPrimary.nominal / 4) 1 x := rfl

end NavierStokes.ActualWaveRegularityData
end
end
