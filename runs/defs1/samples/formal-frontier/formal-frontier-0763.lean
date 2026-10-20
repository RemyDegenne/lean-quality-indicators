@[expose] public section

open scoped MonoidAlgebra TensorProduct

universe u v w w'

namespace MonoidAlgebra

variable (R : Type u) (G : Type v) (M : Type w)
  [CommSemiring R] [Finite G] [AddCommMonoid M] [Module R M]

/-- Finite functions are linearly equivalent to the coefficient module tensored
with the group algebra, with the coefficient module on the left. -/
noncomputable def finiteFunctionTensorLinearEquiv :
    (G → M) ≃ₗ[R] (M ⊗[R] R[G]) := by
  classical
  exact ((TensorProduct.congr (LinearEquiv.refl R M) (coeffLinearEquiv R)) ≪≫ₗ
    TensorProduct.finsuppScalarRight R R M G ≪≫ₗ
    Finsupp.linearEquivFunOnFinite R M G).symm

end MonoidAlgebra
end
