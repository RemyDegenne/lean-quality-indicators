namespace P2MW.S_AutomorphicForm_isClosedEmbedding_unitsMap_includeRight

set_option autoImplicit false

open NumberField

open scoped TensorProduct TensorProduct.RightActions

noncomputable section

namespace K51A1

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A]

theorem retr_tmul (ψ : L →ₗ[K] K) (l : L) (a : A) : retr K L A ψ (l ⊗ₜ[K] a) = ψ l • a := by
  show TensorProduct.lid K A (LinearMap.rTensor A ψ (l ⊗ₜ[K] a)) = _
  rw [LinearMap.rTensor_tmul, TensorProduct.lid_tmul]

end K51A1
end
end P2MW.S_AutomorphicForm_isClosedEmbedding_unitsMap_includeRight
