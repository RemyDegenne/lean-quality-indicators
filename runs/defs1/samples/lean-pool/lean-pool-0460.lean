@[expose] public section

noncomputable section

namespace NavierStokes.ActualGaussianCoverage

open Set Function Filter WeightedClasses

open CommonCoverSolve TorusInverse ParticularWaveBounds PrimaryPulseBounds

open PeriodizedWaveBounds HarmonicCalculus

open scoped Topology ContDiff BigOperators

section Family

variable {Label P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {D : PhaseJetBounds.Domain (Label × ℕ) PhaseCalculus.Slow}
  (F : PhaseConstruction D) (clock : ActualSignedControl.PositiveScale Label)
  (reference : Label → ℕ → Geometry) (gap : Label → ℕ → ℕ)
  (r : Label → ℕ → ℝ) (hr : ∀ l n, 0 < r l n)

/-- Outer family, given by `outerCell (r l n) (F.L (l,n)) (clock.value l n)`. -/
noncomputable def outerFamily (l : Label) (n : ℕ) : Set Plane :=
  outerCell (r l n) (F.L (l,n)) (clock.value l n)

end Family
end NavierStokes.ActualGaussianCoverage
end
end
