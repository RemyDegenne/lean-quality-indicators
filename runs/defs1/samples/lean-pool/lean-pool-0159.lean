section

@[expose] public section

noncomputable section

namespace NavierStokes.InitializedPhysicalBackground

open Set Filter ProblemStatement DiagonalResidual PhysicalStageBounds

open scoped Topology ContDiff BigOperators

/-- The loss for the actual finite initialization potential, before curl.
The offsets absorb its own native homogeneity, without a positivity
assumption on the initialization gain. -/
noncomputable def seedPotentialLoss (h waveAlpha waveShift meanAlpha : ℝ) (m : ℕ) : ℝ :=
  potentialLoss h (-(h * waveAlpha + waveShift)) (-(h * meanAlpha)) m

end NavierStokes.InitializedPhysicalBackground
end
end
end
