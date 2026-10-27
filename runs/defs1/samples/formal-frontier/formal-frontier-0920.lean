@[expose] public section

noncomputable section

open GeneralLinearCoordinateRing

open scoped TensorProduct

universe u

namespace SpecialLinearCoordinateRing

variable (K : Type u) [CommRing K] (n : Type u) [Fintype n] [DecidableEq n]

/-- The determinant-one ideal inside the *localized* general linear coordinate algebra. -/
def determinantOneIdeal : Ideal (CoordinateRing K n) :=
  Ideal.span { (matrix K n).det - 1 }

end SpecialLinearCoordinateRing
end
end
