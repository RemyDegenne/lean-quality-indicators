universe u v

open scoped DirectSum TensorProduct

open Filter Topology

public noncomputable section

namespace LoweringDerivation

variable {E : Type u} {R : Type v} [Field E] [CommRing R] [Algebra E R]

variable (𝒜 : NatOrdinal → Submodule E R) [GradedAlgebra 𝒜]

variable {𝒜}

variable {Δ : R →ₗ[E] FunAtZeroMinus R} (hΔ : IsLoweringDerivation 𝒜 Δ)

section Injectivity

variable (𝒜) in
/-- The element `1 ∈ A_0`. -/
def gradeZeroOne : 𝒜 ((0 : ℕ) : NatOrdinal) := ⟨1, by simp [SetLike.one_mem_graded 𝒜]⟩

end Injectivity
end LoweringDerivation
end
