@[expose] public section

namespace TauCeti

open scoped InnerProductSpace BigOperators

open Module (finrank)

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

theorem selfAdjointFunctionalCalculus_congr
    {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) {f g : ℝ → ℝ}
    (hfg : ∀ i : Fin (finrank 𝕜 E),
      f (hT.eigenvalues rfl i) = g (hT.eigenvalues rfl i)) :
    selfAdjointFunctionalCalculus hT f =
      selfAdjointFunctionalCalculus hT g := by
  apply (hT.eigenvectorBasis rfl).toBasis.ext
  intro i
  simp only [OrthonormalBasis.coe_toBasis,
    selfAdjointFunctionalCalculus_apply_eigenvectorBasis]
  rw [hfg i]

end TauCeti
end
