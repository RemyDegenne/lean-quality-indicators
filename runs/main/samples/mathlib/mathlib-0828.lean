@[expose] public section

universe u v w x y z u' v' w' y'

variable {R : Type u} {M : Type v} {M₂ : Type w}

variable {M₃ : Type y} {M₄ : Type z} {ι : Type x}

variable {M₅ M₆ : Type*}

namespace LinearEquiv

section

variable [Semiring R]

variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃] [AddCommMonoid M₄]

variable {module_M : Module R M} {module_M₂ : Module R M₂}

variable {module_M₃ : Module R M₃} {module_M₄ : Module R M₄}

variable (e₁ : M ≃ₗ[R] M₂) (e₂ : M₃ ≃ₗ[R] M₄)

@[simp]
theorem prodCongr_apply (p) : e₁.prodCongr e₂ p = (e₁ p.1, e₂ p.2) :=
  rfl

end
end LinearEquiv
end
