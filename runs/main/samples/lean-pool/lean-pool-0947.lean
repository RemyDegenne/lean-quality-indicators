@[expose] public section

namespace ContinuousLinearMap

open scoped InnerProductSpace

universe u v

variable {𝕜 : Type*} [RCLike 𝕜]

variable {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

theorem starProjection_comp_modulus (M : E →L[𝕜] F) :
    M.polarInitial.starProjection ∘L M.modulus = M.modulus := by
  ext x
  exact Submodule.starProjection_eq_self_iff.mpr (M.modulus_apply_mem_polarInitial x)

end ContinuousLinearMap
end
