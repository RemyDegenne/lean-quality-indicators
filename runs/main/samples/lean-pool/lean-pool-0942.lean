@[expose] public section

namespace ContinuousLinearMap

open scoped InnerProductSpace

universe u v

variable {𝕜 : Type*} [RCLike 𝕜]

variable {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

theorem adjoint_eq_modulus_comp_adjoint_polarPartial (M : E →L[𝕜] F) :
    M.adjoint = M.modulus ∘L M.polarPartial.adjoint := by
  have h := congrArg ContinuousLinearMap.adjoint M.polarPartial_comp_modulus
  rw [ContinuousLinearMap.adjoint_comp, M.modulus_isSelfAdjoint.adjoint_eq] at h
  exact h.symm

end ContinuousLinearMap
end
