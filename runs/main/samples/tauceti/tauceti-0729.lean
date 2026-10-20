public section

namespace TauCeti

open DirectSum PowerSeries

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]

@[simp]
theorem mem_gradedCompletion_iff {f : PowerSeries A} :
    f ∈ gradedCompletion 𝒜 ↔ ∀ n, coeff n f ∈ 𝒜 n :=
  Iff.rfl

end TauCeti
end
