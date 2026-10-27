@[expose] public section

namespace TauCeti

open scoped InnerProductSpace

open LinearMap InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- The **polar factor** `U` of `A`: the partial isometry that is the isometry `|A| x ↦ A x` on
`range |A| = (ker A)ᗮ`, extended by `0` on `ker A`. Conway VI.3.9. -/
noncomputable def polarFactor (A : E →ₗ[𝕜] E) : E →ₗ[𝕜] E :=
  A ∘ₗ ((ker A)ᗮ).subtype ∘ₗ (operatorAbsRestrict A).symm.toLinearMap
    ∘ₗ (((ker A)ᗮ).orthogonalProjectionOnto : E →L[𝕜] ↥((ker A)ᗮ)).toLinearMap

end TauCeti
end
