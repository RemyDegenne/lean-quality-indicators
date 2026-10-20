public section

open scoped DirectSum

universe u v w

namespace TauCeti.Algebra.wordFiltration

variable {R : Type u} {M : Type v} {A : Type w}

variable [CommRing R] [AddCommMonoid M] [Module R M] [Ring A] [Algebra R A]

variable (f : M →ₗ[R] A)

theorem gradedMul_mem_symbolSubmodule (I : Ideal A) (i j : ℕ) (x : GradedPiece f i)
    {y : GradedPiece f j} (hy : y ∈ symbolSubmodule f I j) :
    gradedMul f i j x y ∈ symbolSubmodule f I (i + j) := by
  induction x using Submodule.Quotient.induction_on with
  | _ a =>
      obtain ⟨b, hb, rfl⟩ := exists_mem_of_mem_symbolSubmodule f hy
      rw [gradedMul_apply_mk]
      exact mk_mem_symbolSubmodule f _ (I.mul_mem_left _ hb)

end TauCeti.Algebra.wordFiltration
end
