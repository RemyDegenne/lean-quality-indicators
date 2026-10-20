public section

noncomputable section

open scoped EuclideanSpace

open Manifold Metric Module Set

open scoped Manifold ContDiff

namespace TauCeti

attribute [local instance] Complex.finrank_real_complex_fact

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

variable {K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)}

theorem isTopologicallySlice_greatCircle (ι : ℂ →ₗᵢ[ℝ] E) :
    IsTopologicallySlice (SmoothCircleEmbedding.greatCircle (n := n) ι) :=
  (isSmoothlySlice_greatCircle ι).isTopologicallySlice

end TauCeti
end
end
