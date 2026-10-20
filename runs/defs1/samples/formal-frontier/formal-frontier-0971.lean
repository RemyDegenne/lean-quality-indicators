@[expose] public section

noncomputable section

open GeneralLinearCoordinateRing

open scoped TensorProduct

universe u

namespace SpecialLinearCoordinateRing

variable (K : Type u) [CommRing K] (n : Type u) [Fintype n] [DecidableEq n]

/-- The coordinate algebra representing determinant-one invertible matrices. -/
abbrev CoordinateRing := GeneralLinearCoordinateRing.CoordinateRing K n ⧸ determinantOneIdeal K n

end SpecialLinearCoordinateRing
end
end
