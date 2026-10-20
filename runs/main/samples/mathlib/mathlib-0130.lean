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

variable {σ : R →+* S}

@[simp]
theorem coe_addHom_mk {σ : R →+* S} (f : AddHom M M₃) (h) :
    ((LinearMap.mk f h : M →ₛₗ[σ] M₃) : AddHom M M₃) = f :=
  rfl

end
end AddCommMonoid
end LinearMap
end
