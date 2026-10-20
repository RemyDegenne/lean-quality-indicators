@[expose] public section

noncomputable section

open scoped TensorProduct

universe u v w x

namespace GeneralLinearCoordinateRing

variable (K : Type u) [CommRing K] (n : Type v) [Fintype n] [DecidableEq n]

/-- The inverse-determinant coordinate. -/
def detInverse : CoordinateRing K n :=
  IsLocalization.Away.invSelf (determinant K n)

end GeneralLinearCoordinateRing
end
end
