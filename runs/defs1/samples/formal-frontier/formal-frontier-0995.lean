@[expose] public section

noncomputable section

open TopologicalSpace

open scoped ContDiff Manifold

universe u v w

namespace ChartedSpace

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
  {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : Type w} [TopologicalSpace M] [ChartedSpace E M]

/-- An open neighborhood with coordinates covering an entire model ball. -/
structure ChartLocalBall (n : ℕ∞ω) (x : M) where
  neighborhood : Opens M
  mem_neighborhood : x ∈ neighborhood
  neighborhood_subset_source : (neighborhood : Set M) ⊆ (chartAt E x).source
  radius : ℝ
  radius_pos : 0 < radius
  coord : neighborhood ≃ₘ^n⟮𝓘(𝕜, E), 𝓘(𝕜, E)⟯ chartBall (E := E) x radius
  coord_apply (point : neighborhood) :
    (coord point : E) = (chartAt E x) point.1
  coord_symm_apply (point : chartBall (E := E) x radius) :
    ((coord.symm point : neighborhood) : M) = (chartAt E x).symm point.1

end ChartedSpace
end
end
