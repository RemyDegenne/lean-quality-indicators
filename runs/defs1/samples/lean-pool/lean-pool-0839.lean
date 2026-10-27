@[expose] public section

noncomputable section

namespace NavierStokes.CorrectionStep

open Set WeightedClasses MeanIncrementBounds

open scoped ContDiff BigOperators

variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]

section ConstructedSignedLinear

open CorrectionState

/-- Good block, constructed using `SignedWaveUpdate.coefficientBlock`. -/
noncomputable def SignedParameters.goodBlock (p : SignedParameters D) (s : StripData D)
    (request : ℕ → D × ℝ → SignedWaveUpdate.Vec2) : HarmonicBlock D :=
  SignedWaveUpdate.coefficientBlock p.base.frequency (fun n x => p.base.phase n (x,0))
      p.angularFrequency
    (fun n x => (p.coefficients s request).constructedGood
      (HarmonicWaveInteraction.productStrip s) p.directions p.cutoff n (x,0)) 0

end ConstructedSignedLinear
end NavierStokes.CorrectionStep
end
end
