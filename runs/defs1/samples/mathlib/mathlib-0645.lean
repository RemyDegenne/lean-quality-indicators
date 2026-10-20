@[expose] public section

variable (R : Type*) [CommSemiring R]

variable (S : Type*) [CommSemiring S] [Algebra R S]

variable (N : Type*) [AddCommMonoid N] [Module R N] [Module S N] [IsScalarTower R S N]

variable (ι : Type*)

open LinearMap

namespace TensorProduct

section

variable {ι} (M : ι → Type*) [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

variable [Fintype ι] [DecidableEq ι]

/-- (Implementation): Inverse for `TensorProduct.piRight`. -/
def piRightInv : (∀ i, N ⊗[R] M i) →ₗ[S] N ⊗[R] ∀ i, M i :=
  LinearMap.lsum S (fun i ↦ N ⊗[R] M i) S <| fun i ↦
    AlgebraTensorModule.map LinearMap.id (single R M i)

end
end TensorProduct
end
