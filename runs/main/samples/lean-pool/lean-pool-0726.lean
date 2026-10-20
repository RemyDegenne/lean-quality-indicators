@[expose] public section

noncomputable section

namespace NavierStokes.CyclePhysicalPrefixes

open Set Filter Function ProblemStatement CorrectionState CorrectionStep

open MeanIncrementBounds

open scoped ContDiff Topology BigOperators

section CartesianStep

variable {ι : Type} (p : CycleParameters ι) (v : CycleCoefficients ι)
    (c : Context CyclePoint) (u : State CyclePoint)
    (a : ℝ) (j : PolarCharts.Index) (G : ScaledGraph) (n : ℕ)

theorem velocity_next :
    velocity a j G n c (p.next v c u) = velocity a j G n c u + stepVelocity p v c u a j G n := by
  simp only [velocity, stepVelocity, cylindricalVelocity_next, map_add]

end CartesianStep
end NavierStokes.CyclePhysicalPrefixes
end
end
