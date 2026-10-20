@[expose] public section

noncomputable section

open GeneralLinearCoordinateRing

open scoped TensorProduct

universe u

namespace SpecialLinearCoordinateRing

variable (K : Type u) [CommRing K] (n : Type u) [Fintype n] [DecidableEq n]

/-- The determinant-one ideal in the polynomial matrix coordinate ring. -/
def polynomialIdeal : Ideal (PolynomialRing K n) :=
  Ideal.span {determinant K n - 1}

end SpecialLinearCoordinateRing
end
end
