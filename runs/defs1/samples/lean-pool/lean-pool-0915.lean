@[expose] public section

noncomputable section

namespace NavierStokes.ActualPeriodizedSignedRealization

open Set Function Filter

open HarmonicCalculus LinearWaveBounds WeightedClasses

open ProblemStatement

open scoped Topology ContDiff BigOperators InnerProductSpace

section Reference

variable {U : PhaseJetBounds.Domain ℕ PhaseCalculus.Slow}
  (B : PhysicalSignedWave.PrimaryData U) (l : Layout)

variable {reference : ℕ} (V : B.Views reference)

/-- Physical pressure, given by `(views B l V).physicalPressure D.referenceRequest j delta`. -/
noncomputable def physicalPressure (D : V.StateData) (j : Fin 2) (delta : ℝ) : PressureField :=
  (views B l V).physicalPressure D.referenceRequest j delta

end Reference
end NavierStokes.ActualPeriodizedSignedRealization
end
end
