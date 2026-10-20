section

@[expose] public section

noncomputable section

namespace NavierStokes.GaussianErrorNaturality

open Set Filter Function HarmonicCalculus LinearWaveBounds

open scoped Topology ContDiff

section ActualReference

open CommonCoverSolve TorusInverse ParticularWaveAssembly ParticularWaveBounds

open CorrectionState PhysicalParticularWave

theorem fromReference_globalGaussian (D : AssemblyData Parameter) (h : ℝ) (gap : ℕ → ℕ)
    (j : ℤ) (n i : ℕ)
    (H : PhysicalResidualNaturality.BandCoherence D h (ChartScales.Q_pos n)
      (ChartScales.Q_pos D.reference.band) i (gap n) n)
    (hn : PhysicalResidualNaturality.PositiveSupport D.carrierBlock D.gaussianInput D.aliasInput n)
    (hr : PhysicalResidualNaturality.PositiveSupport D.carrierBlock D.gaussianInput D.aliasInput
        D.reference.band)
    {U : Set Parameter} (R : ReferenceODE D j U) (hcutoff : ContDiff ℝ ∞ D.reference.cutoff)
    (hK : (j : ℝ) * D.carrierBlock.frequency n ≠ 0) (hKr : referenceFrequency D j ≠ 0)
    (hfast : waveChange h (ChartScales.Q n) (ChartScales.Q D.reference.band) (gap n)
      (D.directions.fastScale n • D.directions.fast) =
      clockWeight h (ChartScales.Q n) (ChartScales.Q D.reference.band) •
        (D.directions.fastScale D.reference.band • D.directions.fast))
    (x : WaveSpace)
    (hx : parameterChange h (ChartScales.Q n) (ChartScales.Q D.reference.band) x.1.1 ∈ U) :
    (nativeData D h gap j).globalGaussian D.directions n x =
      sourceWeight h (ChartScales.Q n) (ChartScales.Q D.reference.band) •
        (referenceData D j).globalGaussian D.directions D.reference.band
          (waveChange h (ChartScales.Q n) (ChartScales.Q D.reference.band) (gap n) x) := by
  rw [← clock_mul_velocity (ChartScales.Q_pos n) (ChartScales.Q_pos D.reference.band)]
  apply globalGaussian_transport _ D.directions D.directions _ _ n D.reference.band _ _ x
    (native_cutoff_transport D h gap j n) hfast
  · exact fun copy => reference_cutoff_differentiable D j hcutoff copy _
  · intro copy hcopy
    exact native_amplitude_transport D h gap j n i H hn hr R hK hKr copy x hx
      (current_slot_of_reference_derivative D h gap j n R copy x hcopy)
  · exact native_source_transport D h gap j n i H hn hr x

end ActualReference
end NavierStokes.GaussianErrorNaturality
end
end
end
