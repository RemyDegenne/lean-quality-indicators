section

@[expose] public section

noncomputable section

namespace NavierStokes.ActualWaveRegularity

open Set Function Filter WeightedClasses HarmonicCalculus LinearWaveBounds

open PeriodizedWaveBounds CorrectionState

open CurlClassBounds hiding ComplexVector

open scoped Topology ContDiff BigOperators

variable {D I : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]

section SignedCycle

open CorrectionStep CopyAngularInvariance

theorem SignedData.block_regular {ι : Type} {p : CycleParameters ι} {v : CycleCoefficients ι}
    {c : Context Point} {u : State Point} {coord r₀ r₁ : ℝ}
    {U : LocalSignedRequest.SlowRegion coord} (h : SignedData p v c u U r₀ r₁) (l : ι) :
    WaveStateRegularity.AngularSmooth (PhysicalMeanDomain.slowDomain U.carrier)
      (p.signedBlock v c u l).oscillation ∧
    OscillationPeriodic U.carrier (p.signedBlock v c u l).oscillation ∧
    WaveStateRegularity.WaveSupport U r₀ r₁ (p.signedBlock v c u l).oscillation := by
  unfold CycleParameters.signedBlock
  rw [(h.angles l).block_eq_mode]
  exact (h.mode l).regular

end SignedCycle
end NavierStokes.ActualWaveRegularity
end
end
end
