@[expose] public section

noncomputable section

namespace NavierStokes.ScaledActualParticularControl

open Set Function Filter WeightedClasses PhaseJetBounds PrimaryPulseBounds

open CommonCoverSolve TorusInverse ParticularWaveBounds LabelSumBounds

open ActualParticularControl

open scoped Topology ContDiff InnerProductSpace BigOperators

variable {Label P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {D : PhaseJetBounds.Domain (Label × ℕ) Slow}

/-- Physical phi, given by `ActualSignedGeometry.slowChange h (ChartScales.Q (chart i.2))
(ChartScales.Q (reference i.1 i.2))`. -/
noncomputable def physicalPhi (h : ℝ) (chart : ℕ → ℕ) (reference : Label → ℕ → ℕ)
    (i : Label × ℕ) : Slow →L[ℝ] Slow :=
  ActualSignedGeometry.slowChange h (ChartScales.Q (chart i.2)) (ChartScales.Q (reference i.1 i.2))

end NavierStokes.ScaledActualParticularControl
end
end
