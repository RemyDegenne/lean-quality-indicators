@[expose] public section

noncomputable section

open scoped TensorProduct

universe uK uE₁ uE₂

namespace TopModuleCat

section FiniteLeft

variable (𝕜 : Type uK) [NontriviallyNormedField 𝕜]

variable (E : Type uE₁) [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]

variable [IsModuleTopology 𝕜 E]

variable (G : Type uE₂) [AddCommGroup G] [Module 𝕜 G] [TopologicalSpace G]

variable [IsTopologicalAddGroup G] [ContinuousSMul 𝕜 G]

variable {ι : Type*} [Fintype ι]

variable [FiniteDimensional 𝕜 E]

theorem continuous_dualTensorHom_inverse :
    Continuous (LinearEquiv.ofBijective (dualTensorHom 𝕜 E G).toLinearMap
      (dualTensorHom_bijective 𝕜 E G)).symm := by
  let e := dualTensorHomEquiv 𝕜 E G
  have he : e.toLinearEquiv = LinearEquiv.ofBijective (dualTensorHom 𝕜 E G).toLinearMap
      (dualTensorHom_bijective 𝕜 E G) := by
    apply LinearEquiv.toLinearMap_injective
    exact congrArg ContinuousLinearMap.toLinearMap
      (dualTensorHomEquiv_toContinuousLinearMap 𝕜 E G)
  exact e.symm.continuous.congr (fun A ↦
    congrArg (fun g : StrongDual 𝕜 E ⊗[𝕜] G ≃ₗ[𝕜] (E →L[𝕜] G) ↦ g.symm A) he)

end FiniteLeft
end TopModuleCat
end
end
