section

@[expose] public section

noncomputable section

namespace NavierStokes.GaussianErrorNaturality

open Set Filter Function HarmonicCalculus LinearWaveBounds

open scoped Topology ContDiff

section ReferenceData

open CommonCoverSolve TorusInverse ParticularWaveAssembly ParticularWaveBounds

open CorrectionState

/-- The full native change of variables, conjugate to the actual
cylindrical change of band and common cover. -/
noncomputable def waveChange (h Q Qr : ℝ) (gap : ℕ) : WaveSpace →L[ℝ] WaveSpace :=
  PhysicalParticularWave.waveEquiv.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((PhysicalParticularWave.cylinderChange h Q Qr gap).comp
      PhysicalParticularWave.waveEquiv.symm.toContinuousLinearEquiv.toContinuousLinearMap)

end ReferenceData
end NavierStokes.GaussianErrorNaturality
end
end
end
