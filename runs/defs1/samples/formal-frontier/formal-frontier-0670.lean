@[expose] public section

open Polynomial

namespace FrobeniusTwistedLine

open scoped TensorProduct

noncomputable section

variable (K : Type*) [Field K]

/-- The `X` coordinate in `CoordinateRing`. -/
def x (p : ℕ) (t : K) : CoordinateRing K p t :=
  Ideal.Quotient.mk _ (MvPolynomial.X 1)

end
end FrobeniusTwistedLine
end
