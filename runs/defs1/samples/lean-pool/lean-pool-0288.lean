@[expose] public section

noncomputable section

namespace NavierStokes.ActualGaussianCoverage

open Set Function Filter WeightedClasses

open CommonCoverSolve TorusInverse ParticularWaveBounds PrimaryPulseBounds

open PeriodizedWaveBounds HarmonicCalculus

open scoped Topology ContDiff BigOperators

/-- Reference cutoff, given by `(referenceWindow r L hr hL).cutoff z *
GaussianTailFlat.slotCutoff L z.2`. -/
noncomputable def referenceCutoff (r L : ℝ) (hr : 0 < r) (hL : 0 < L) (z : Plane) : ℝ :=
  (referenceWindow r L hr hL).cutoff z * GaussianTailFlat.slotCutoff L z.2

end NavierStokes.ActualGaussianCoverage
end
end
