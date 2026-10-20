@[expose] public section

open scoped MonoidAlgebra

namespace Representation

variable {A G V W U : Type*} [CommSemiring A] [Monoid G] [AddCommMonoid V] [AddCommMonoid W]
  [AddCommMonoid U] [Module A V] [Module A W] [Module A U] (ρ : Representation A G V)
  (σ : Representation A G W) (τ : Representation A G U) (f : V →ₗ[A] W)

section Monoid

namespace IntertwiningMap

variable {P : Type*} [AddCommMonoid P] [Module A P] {π : Representation A G P}

variable {ρ σ τ}

@[simp]
lemma rTensor_smul (a : A) (f : IntertwiningMap σ τ) :
    rTensor ρ (a • f) = a • rTensor ρ f := tensor_smul_left _ _ _

end IntertwiningMap
end Monoid
end Representation
end
