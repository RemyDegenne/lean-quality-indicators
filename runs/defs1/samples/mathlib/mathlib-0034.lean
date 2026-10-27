@[expose] public section

open Function

universe u u' v w

variable {R R₁ R₂ R₃ S S₃ T M M₁ M₂ M₃ N₂ N₃ : Type*}

notation:25 M " →ₛₗ[" σ:25 "] " M₂:0 => LinearMap σ M M₂

notation:25 M " →ₗ[" R:25 "] " M₂:0 => LinearMap (RingHom.id R) M M₂

namespace LinearMap

section AddCommMonoid

variable [Semiring R] [Semiring S]

section

variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]

variable [Module R M] [Module R M₂] [Module S M₃]

variable (σ : R →+* S)

variable (fₗ : M →ₗ[R] M₂) (f g : M →ₛₗ[σ] M₃)

variable {fₗ f g σ}

variable (fₗ f g)

variable (M M₂)

variable {M M₂}

/-- Convert a linear map to an additive monoid hom. -/
-- See note [implicit instance arguments]
def toAddMonoidHom {modM₁ : Module R M₁} {modM₂ : Module S M₂} {σ : R →+* S} (f : M₁ →ₛₗ[σ] M₂) :
    M₁ →+ M₂ where
  toFun := f
  map_zero' := f.map_zero
  map_add' := f.map_add

end
end AddCommMonoid
end LinearMap
end
