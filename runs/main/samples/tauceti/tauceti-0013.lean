public section

noncomputable section

open scoped InnerProduct

namespace ContinuousLinearMap

section Adjoint

variable {𝕜 E F G : Type*} [RCLike 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
  {T : E →L[𝕜] F} {A : E →L[𝕜] G}

theorem norm_factorThru_apply_of_denseRange (h : ∀ x, ‖T x‖ = ‖A x‖) (hA : DenseRange A)
    (y : G) : ‖T.factorThru A y‖ = ‖y‖ := by
  refine norm_factorThru_apply h ?_
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
  exact hA.closure_range ▸ Set.mem_univ y

end Adjoint
end ContinuousLinearMap
end
end
