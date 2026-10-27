public section

open Filter Function Set Topology

open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {f : M → ℝ} {x : M} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

namespace MorseChart

variable (φ : MorseChart E f x)

/-- The **stable subspace** of a Morse chart: the vectors whose coordinates of negative weight
vanish. -/
noncomputable def stableSubspace : Submodule ℝ E :=
  LinearMap.ker φ.negativeCoord

end MorseChart
end TauCeti
end
