public section

namespace SymmetricAlgebra

open TauCeti.SymmetricAlgebra

universe u v w x

variable (R : Type u) [CommSemiring R]

variable {M : Type v} {N : Type w} {P : Type x}

variable [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

variable [AddCommMonoid P] [Module R P]

section GradedLift

variable {A : Type*} [CommSemiring A] [Algebra R A] (𝒜 : ℕ → Submodule R A)
  [SetLike.GradedMonoid 𝒜]

theorem gradedLift_ι (f : M →ₗ[R] 𝒜 1) (m : M) : gradedLift R 𝒜 f (ι R M m) = f m := by
  simp

end GradedLift
end SymmetricAlgebra
end
