@[expose] public section

open scoped BigOperators ContDiff

open Complex Real MeasureTheory

noncomputable
section

namespace NashEmbedding.Sobolev

variable {n : ℕ}

/-- The (flat) Laplacian `Δg = ∑ⱼ ∂ⱼ∂ⱼ g`. -/
def laplacian (g : (Fin n → ℝ) → ℂ) : (Fin n → ℝ) → ℂ :=
  fun θ => ∑ j, partialDeriv j (partialDeriv j g) θ

end NashEmbedding.Sobolev
end
end
