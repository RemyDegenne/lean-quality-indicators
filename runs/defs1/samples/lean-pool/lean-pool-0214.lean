@[expose] public section

open TauCeti.DavisKahan.Sylvester

open scoped InnerProductSpace

namespace TauCeti

namespace DavisKahan

open Module (finrank)

open Module.End (eigenspace)

universe u v

variable {𝕜 : Type*} [RCLike 𝕜]

section TwoSpaces

variable {H₁ : Type u} [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁]
  [CompleteSpace H₁]

variable {H₂ : Type v} [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂]
  [CompleteSpace H₂]

variable (U₁ V₁ : Submodule 𝕜 H₁) [U₁.HasOrthogonalProjection]
  [V₁.HasOrthogonalProjection]

variable (U₂ V₂ : Submodule 𝕜 H₂) [U₂.HasOrthogonalProjection]
  [V₂.HasOrthogonalProjection]

/-- **Davis--Kahan 1970 Corollary 3.1's invariant.**  The four elementary Halmos
multiplicities, together with the multiplicity of every angle: the paper's
decreasing eigenvalue list, written as a dimension function. -/
structure SameCompactAngleData : Prop where
  common : Nonempty (halmosCommonPart U₁ V₁ ≃ₗᵢ[𝕜] halmosCommonPart U₂ V₂)
  sourceDefect : Nonempty
    (halmosSourceDefect U₁ V₁ ≃ₗᵢ[𝕜] halmosSourceDefect U₂ V₂)
  targetDefect : Nonempty
    (halmosTargetDefect U₁ V₁ ≃ₗᵢ[𝕜] halmosTargetDefect U₂ V₂)
  exterior : Nonempty (halmosExteriorPart U₁ V₁ ≃ₗᵢ[𝕜] halmosExteriorPart U₂ V₂)
  angleMultiplicity : ∀ μ : 𝕜,
    finrank 𝕜 (eigenspace (genericCosineBlock U₁ V₁).toLinearMap μ) =
      finrank 𝕜 (eigenspace (genericCosineBlock U₂ V₂).toLinearMap μ)

end TwoSpaces
end DavisKahan
end TauCeti
end
