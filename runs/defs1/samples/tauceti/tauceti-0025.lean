public section

open Module

variable {𝕜 E F E' F' : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E'] [NormedAddCommGroup F']
  [InnerProductSpace 𝕜 F']

namespace TauCeti

namespace UnitarilyInvariantSeminorm

variable (N : UnitarilyInvariantSeminorm 𝕜 E F)

/-- **Transport** of unitarily invariant seminorms along isometric isomorphisms `eE : E ≃ E'` of
the sources and `eF : F ≃ F'` of the targets: `N` corresponds to the seminorm
`A ↦ N (eF⁻¹ ∘ A ∘ eE)` on `E' →ₗ[𝕜] F'`, which is again unitarily invariant. -/
noncomputable def arrowCongr (eE : E ≃ₗᵢ[𝕜] E') (eF : F ≃ₗᵢ[𝕜] F') :
    UnitarilyInvariantSeminorm 𝕜 E F ≃ UnitarilyInvariantSeminorm 𝕜 E' F' where
  toFun := transport eE eF
  invFun := transport eE.symm eF.symm
  left_inv N := by ext; rw [transport_apply, transport_apply]; congr 1; ext; simp
  right_inv N := by ext; rw [transport_apply, transport_apply]; congr 1; ext; simp

end UnitarilyInvariantSeminorm
end TauCeti
end
