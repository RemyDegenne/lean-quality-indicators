public section

open Filter Set MeasureTheory Metric

open scoped ENNReal Topology

namespace SeveralComplexVariables

variable {ι F : Type*} [Fintype ι] [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Holomorphic Lp functions, represented as a subspace of Mathlib's Lebesgue Lp space. For `1 ≤ p`
the norm and complex normed-space structure are inherited from Lp. -/
abbrev HolomorphicLp (U : TopologicalSpace.Opens (ι → ℂ)) (F : Type*)
    [NormedAddCommGroup F] [NormedSpace ℂ F] (p : ℝ≥0∞) : Type _ :=
  ↥(holomorphicLpSubmodule (F := F) U p)

end SeveralComplexVariables
end
