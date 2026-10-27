public section

noncomputable section

open scoped TensorProduct

namespace TauCeti.ConstructionA

open Matrix

variable (m : ℕ) {ι : Type*}

/-- The rational-linear embedding into real coordinates scaled by `1 / √m`. -/
def realEmbedding : (ι → ℚ) →ₗ[ℚ] (ι → ℝ) :=
  (Real.sqrt (m : ℝ))⁻¹ • (Algebra.linearMap ℚ ℝ).compLeft ι

end TauCeti.ConstructionA
end
end
