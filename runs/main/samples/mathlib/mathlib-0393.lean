@[expose] public section

open Module Submodule

noncomputable section

namespace LinearMap

section Projective

variable {R : Type*} [CommSemiring R]

variable {M : Type*} [AddCommMonoid M] [Module R M] [Projective R M]

protected theorem Nondegenerate.id : Nondegenerate (M₁ := M →ₗ[R] R) .id :=
  ⟨.id, .id⟩

end Projective
end LinearMap
end
end
