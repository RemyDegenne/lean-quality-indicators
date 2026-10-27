public section

noncomputable section

open scoped ENNReal FourierTransform SchwartzMap RealInnerProductSpace Real Laplacian LineDeriv

open FourierTransform MeasureTheory

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The symbol `ξ ↦ ⟪ξ, v⟫ ⟪ξ, w⟫ / ‖ξ‖²` of the operator `∂_v ∂_w Δ⁻¹`. At the origin it takes
the value `0`. -/
def hessianSymbol (v w : E) (ξ : E) : ℂ :=
  ((⟪ξ, v⟫ * ⟪ξ, w⟫ / ‖ξ‖ ^ 2 : ℝ) : ℂ)

end TauCeti
end
end
