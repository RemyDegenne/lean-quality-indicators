@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

open scoped ContDiff Manifold

universe u

namespace FiniteRegularityFunctions

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
  {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : Type u} [TopologicalSpace M] [ChartedSpace E M]

/-- The genuine open ball centered at the coordinate of a point in its chosen chart. -/
def chartBall (x : M) (radius : ℝ) : Opens E :=
  ChartedSpace.chartBall x radius

end FiniteRegularityFunctions
end
end
