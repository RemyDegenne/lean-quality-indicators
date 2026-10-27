public section

open scoped DirectSum

universe u v w

namespace TauCeti.Algebra.wordFiltration

variable {R : Type u} {M : Type v} {A : Type w}

variable [CommRing R] [AddCommMonoid M] [Module R M] [Ring A] [Algebra R A]

variable (f : M →ₗ[R] A)

/-- The **degree-`n` symbols** of a left ideal `I` of a word-filtered algebra: the classes in the
degree-`n` graded piece of the elements of `I` of filtration degree at most `n`. -/
def symbolSubmodule (I : Ideal A) (n : ℕ) : Submodule R (GradedPiece f n) :=
  ((I.restrictScalars R).comap (wordFiltration f n).subtype).map
    (previousRestricted f n).mkQ

end TauCeti.Algebra.wordFiltration
end
