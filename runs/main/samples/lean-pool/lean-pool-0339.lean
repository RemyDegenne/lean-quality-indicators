@[expose] public section

namespace RS

open scoped TensorProduct

universe u u' v w w'

section GradedBlocks

variable (P Q : Type*)

@[simp]
theorem tensorLeftSwap_apply
    [AddCommGroup P] [Module ℂ P] [AddCommGroup Q] [Module ℂ Q] {A : Type*}
    {X₁ : Type*} {X₂ : Type*} {Y₁ : Type*} {Y₂ : Type*} [AddCommGroup A]
    [Module ℂ A] [AddCommGroup X₁] [Module ℂ X₁] [AddCommGroup X₂]
    [Module ℂ X₂] [AddCommGroup Y₁] [Module ℂ Y₁] [AddCommGroup Y₂]
    [Module ℂ Y₂]
    (f : A →ₗ[ℂ] X₁ →ₗ[ℂ] X₂)
    (g : A →ₗ[ℂ] Y₁ →ₗ[ℂ] Y₂) (a : A)
    (t : (X₁ ⊗[ℂ] P) × (Y₁ ⊗[ℂ] Q)) :
    tensorLeftSwap P Q f g a t =
      ((g a).rTensor Q t.2, (f a).rTensor P t.1) := rfl

end GradedBlocks
end RS
end
