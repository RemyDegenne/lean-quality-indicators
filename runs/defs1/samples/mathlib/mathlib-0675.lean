@[expose] public section

open Function Set

variable {R : Type*} {R₂ : Type*} {R₃ : Type*}

variable {M : Type*} {M₂ : Type*} {M₃ : Type*}

namespace Submodule

section AddCommMonoid

variable [Semiring R] [Semiring R₂] [Semiring R₃]

variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]

variable [Module R M] [Module R₂ M₂] [Module R₃ M₃]

variable {σ₁₂ : R →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R →+* R₃}

variable [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

variable (p p' : Submodule R M) (q q' : Submodule R₂ M₂)

variable {x : M}

section SemilinearMap

variable {σ₂₁ : R₂ →+* R} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]

/-- The pullback of a submodule `p ⊆ M₂` along `f : M → M₂` -/
@[implicit_reducible]
def comap (f : M →ₛₗ[σ₁₂] M₂) (p : Submodule R₂ M₂) : Submodule R M :=
  { p.toAddSubmonoid.comap f with
    carrier := f ⁻¹' p
    -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 added `map_smulₛₗ _`
    smul_mem' := fun a x h => by simp [p.smul_mem (σ₁₂ a) h, map_smulₛₗ _] }

end SemilinearMap
end AddCommMonoid
end Submodule
end
