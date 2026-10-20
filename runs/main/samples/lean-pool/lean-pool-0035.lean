@[expose] public section

noncomputable section

namespace NavierStokes.ActualCurrentParticularPhysical

open Set Function Filter ProblemStatement HarmonicCalculus

open CorrectionState CorrectionStep CorrectionInitialization

open scoped Topology ContDiff BigOperators

variable {B N0 : ℕ}

theorem cylindricalPressure_contDiffAt_of_native (x : CycleState (Label B N0))
    (l : Label B N0) (j : ℤ) (n : ℕ) {z : SpaceTime} (hr : 0 < z.2 0)
    (hP : ContDiffAt ℝ ∞ (fun v => (nativePressure x l j n v).re)
      (PhysicalParticularWave.nativeMap CorrectionInitialization.ActualPrimary.h
        (ChartScales.Q n) (CommonWindow.index CorrectionInitialization.ActualPrimary.h n) z)) :
    ContDiffAt ℝ ∞ (cylindricalPressure x l j n) z :=
  contDiffAt_const.mul (hP.comp z (nativeMap_contDiffAt n hr))

end NavierStokes.ActualCurrentParticularPhysical
end
end
