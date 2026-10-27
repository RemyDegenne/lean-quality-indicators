@[expose] public section

noncomputable section

open TopologicalSpace

open scoped ContDiff Manifold

universe u v w

namespace ChartedSpace

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
  {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : Type w} [TopologicalSpace M] [ChartedSpace E M]

namespace ChartLocalBall

variable {n : ℕ∞ω} {x : M} (b : ChartLocalBall (𝕜 := 𝕜) (E := E) n x)

/-- The full ball targeted by the coordinate diffeomorphism. -/
abbrev ball : Opens E := chartBall (E := E) x b.radius

end ChartLocalBall
end ChartedSpace
end
end
