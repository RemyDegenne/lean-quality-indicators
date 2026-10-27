public section

open Module (finrank)

open scoped InnerProductSpace

namespace TauCeti

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [Fintype ι]

variable (𝕜) in
/-- The frame operator `x ↦ ∑ᵢ ⟪vᵢ, x⟫ vᵢ` of a finite family: synthesis after analysis. -/
noncomputable def frameOperator (v : ι → E) : E →ₗ[𝕜] E :=
  synthesisMap 𝕜 v ∘ₗ analysisMap 𝕜 v

end TauCeti
end
