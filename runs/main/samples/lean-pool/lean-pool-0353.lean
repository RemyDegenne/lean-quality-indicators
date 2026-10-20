@[expose] public section

attribute [local instance] FiniteDimensional.hasContDiffBump

noncomputable section

open Set Filter Function Metric

open scoped Topology ContDiff BigOperators

namespace NavierStokes.SpatialBorelExtension

variable {X V : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [NormedAddCommGroup V] [NormedSpace ℝ V]

section Family

variable (a : ℕ → X → V) (ha : ∀ j, ContDiff ℝ ∞ (a j))

theorem scale_doubling (j : ℕ) : 2 * scale a ha j ≤ scale a ha (j + 1) :=
  DiagonalScale.doublingEnvelope_growth (localScale a ha) j

end Family
end NavierStokes.SpatialBorelExtension
end
end
