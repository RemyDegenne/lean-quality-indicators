@[expose] public section

namespace TauCeti

open scoped InnerProductSpace BigOperators

open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

section SourceBasis

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]

theorem sum_sq_principalCosines_eq_sum_sq_norm_projection (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (b : OrthonormalBasis (Fin (finrank 𝕜 U)) 𝕜 U) :
    ∑ i : Fin (finrank 𝕜 U), principalCosines U V (i : ℕ) ^ 2 =
      ∑ i, ‖projection V ((b i : U) : E)‖ ^ 2 := by
  have happ : ∀ i, (cosThetaMap U V ∘ₗ U.subtype) (b i) =
      projection V ((b i : U) : E) := by
    intro i
    -- exposes the inner projection, which is the identity on a vector of `U`.
    change V.starProjection (U.starProjection ((b i : U) : E)) =
      V.starProjection ((b i : U) : E)
    rw [U.starProjection_eq_self_iff.mpr (b i).2]
  rw [← singularValues_cosThetaMap_comp_subtype U V,
    sum_sq_singularValues (cosThetaMap U V ∘ₗ U.subtype) rfl b]
  simp only [happ]

end SourceBasis
end TauCeti
end
