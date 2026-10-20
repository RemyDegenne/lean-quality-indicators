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

theorem dualTensorHomEquiv_symm_apply (e : Module.Basis ι 𝕜 E) (A : E →L[𝕜] G) :
    (dualTensorHomEquiv 𝕜 E G).symm A =
      ∑ i, (show TopModuleCat.tensorLeftObj 𝕜 (ModuleCat.of 𝕜 (StrongDual 𝕜 E))
        (TopModuleCat.of 𝕜 G) from
        (⟨e.coord i, IsModuleTopology.continuous_of_linearMap (e.coord i)⟩ :
          StrongDual 𝕜 E) ⊗ₜ[𝕜] A (e i)) := by
  apply (dualTensorHomEquiv 𝕜 E G).injective
  calc
    dualTensorHomEquiv 𝕜 E G ((dualTensorHomEquiv 𝕜 E G).symm A) = A :=
      (dualTensorHomEquiv 𝕜 E G).apply_symm_apply A
    _ = dualTensorHom 𝕜 E G (dualTensorHomInverseOfBasis 𝕜 E G e A) :=
      (dualTensorHom_inverseOfBasis 𝕜 E G e A).symm
    _ = dualTensorHomEquiv 𝕜 E G
        (∑ i, (show TopModuleCat.tensorLeftObj 𝕜 (ModuleCat.of 𝕜 (StrongDual 𝕜 E))
          (TopModuleCat.of 𝕜 G) from
          (⟨e.coord i, IsModuleTopology.continuous_of_linearMap (e.coord i)⟩ :
            StrongDual 𝕜 E) ⊗ₜ[𝕜] A (e i))) := by
      rw [dualTensorHomInverseOfBasis_apply, dualTensorHomEquiv_apply]

end FiniteLeft
end TopModuleCat
end
end
