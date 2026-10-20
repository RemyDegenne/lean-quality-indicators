@[expose] public section

noncomputable section

namespace NavierStokes.CyclePhysicalPrefixes

open Set Filter Function ProblemStatement CorrectionState CorrectionStep

open MeanIncrementBounds

open scoped ContDiff Topology BigOperators

section OneStep

variable {ι : Type} (p : CycleParameters ι) (v : CycleCoefficients ι)
    (c : Context CyclePoint) (u : State CyclePoint)

theorem cylindricalPressure_difference (G : ScaledGraph) (n : ℕ) (p₀ : Cylinder → ℝ) :
    cylindricalPressure G n p₀ (p.next v c u) - cylindricalPressure G n p₀ u =
      cylindricalStepPressure p v c u G n := by
  rw [cylindricalPressure_next]
  abel

end OneStep
end NavierStokes.CyclePhysicalPrefixes
end
end
