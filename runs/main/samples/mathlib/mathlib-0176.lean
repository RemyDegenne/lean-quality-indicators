@[expose] public section

open Function Module

namespace LinearMap

section Semiring

variable {R R₂ S S₂ : Type*} [Semiring R] [Semiring R₂] [Semiring S] [Semiring S₂]

variable {M M₂ N N₂ P P₂ Pₗ : Type*} [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid N]

variable [AddCommMonoid N₂] [AddCommMonoid P] [AddCommMonoid P₂] [AddCommMonoid Pₗ]

variable [Module R M] [Module R M₂] [Module S N] [Module S N₂] [Module R₂ P] [Module S₂ P]

variable [Module R P₂] [Module S₂ P₂] [Module R Pₗ] [Module S Pₗ]

variable {M' P' : Type*} [AddCommGroup M'] [AddCommGroup P']

variable [Module R M'] [Module R₂ P'] [Module S₂ P']

variable [SMulCommClass S₂ R₂ P] [SMulCommClass S R Pₗ] [SMulCommClass S₂ R₂ P']

variable [SMulCommClass S₂ R P₂]

variable {ρ₁₂ : R →+* R₂} {σ₁₂ : S →+* S₂}

variable (ρ₁₂ σ₁₂)

variable {ρ₁₂ σ₁₂}

variable (R S)

variable {R S}

attribute [local instance] SMulCommClass.symm

theorem map_smulₛₗ₂ (f : M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P) (r : R) (x y) : f (r • x) y = ρ₁₂ r • f x y :=
  (flip f y).map_smulₛₗ _ _

end Semiring
end LinearMap
end
