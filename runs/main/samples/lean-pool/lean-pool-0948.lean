@[expose] public section

noncomputable section

namespace NavierStokes.ActualCyclePeriodicity

open Set Function Filter CorrectionState CorrectionStep CorrectionInitialization

open HarmonicFields HarmonicResidual

open ActualWaveRegularity

open scoped Topology ContDiff BigOperators ComplexConjugate

theorem initial (B N0 : ℕ) : Periodic (ActualInitialization.initialCycleState B N0) where
  velocity l n hn k i j z _ :=
    ActualSeedPeriodicity.primary_velocity_periodic l n hn i j k z
  pressure l n hn k j z _ :=
    ActualSeedPeriodicity.primary_pressure_periodic l n hn j k z
  gaussian l n hn k i j z _ :=
    ActualSeedPeriodicity.gaussian_velocity_periodic l n hn i j k z

end NavierStokes.ActualCyclePeriodicity
end
end
