public section

open scoped DirectSum

universe u v w

namespace TauCeti.Algebra.wordFiltration

variable {R : Type u} {M : Type v} {A : Type w}

variable [CommRing R] [AddCommMonoid M] [Module R M] [Ring A] [Algebra R A]

variable (f : M →ₗ[R] A)

theorem exists_mem_of_mem_symbolSubmodule {I : Ideal A} {n : ℕ} {z : GradedPiece f n}
    (hz : z ∈ symbolSubmodule f I n) :
    ∃ a : wordFiltration f n, (a : A) ∈ I ∧
      (Submodule.Quotient.mk a : GradedPiece f n) = z := by
  obtain ⟨a, ha, rfl⟩ := hz
  exact ⟨a, ha, rfl⟩

end TauCeti.Algebra.wordFiltration
end
