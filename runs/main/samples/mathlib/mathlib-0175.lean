@[expose] public section

open Function LinearMap Matrix Module TensorProduct

variable {ι R M N P Q : Type*}

attribute [local ext high] TensorProduct.ext

section Contraction

section CommSemiring

variable [CommSemiring R]

variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P] [AddCommMonoid Q]

variable [Module R M] [Module R N] [Module R P] [Module R Q]

@[simp]
theorem contractLeft_apply (f : Module.Dual R M) (m : M) : contractLeft R M (f ⊗ₜ m) = f m :=
  rfl

end CommSemiring
end Contraction
end
