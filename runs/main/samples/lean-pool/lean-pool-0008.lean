@[expose] public section

noncomputable section

namespace NavierStokes.ActualCurrentWaveSupport

open Set Function Filter ProblemStatement CorrectionInitialization

open scoped Topology BigOperators

section CurrentCoordinates

theorem nativePoint_radius (n : ℕ) (w : SpaceTime) :
    (ActualCurrentParticularPhysical.nativePoint n w).1.1.1 =
      (ChartScales.Q n) ^ (-(1 / 2 : ℝ)) * AnnularEndpoint.radius w := by
  simp only [ActualCurrentParticularPhysical.nativePoint, PhysicalParticularWave.nativeMap,
    PhysicalParticularWave.waveEquiv_apply, PhysicalResidualBridge.ScaledGraph.map,
    ActualCurrentParticularPhysical.cylinderPoint, AxisymmetricResidual.pack_zero,
    PhysicalResidualBridge.commonGraph, AnnularEndpoint.radius]

end CurrentCoordinates
end NavierStokes.ActualCurrentWaveSupport
end
end
