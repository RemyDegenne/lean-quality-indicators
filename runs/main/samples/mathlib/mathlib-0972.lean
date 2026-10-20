open scoped Finset

@[expose] public section

noncomputable section

open Set LinearMap Submodule

variable {R : Type*} {M : Type*} {N : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

open Finsupp

theorem LinearMap.map_finsupp_linearCombination (f : M →ₗ[R] N) {ι : Type*} {g : ι → M}
    (l : ι →₀ R) : f (linearCombination R g l) = linearCombination R (f ∘ g) l :=
  apply_linearCombination _ _ _ _

end
end
