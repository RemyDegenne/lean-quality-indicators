@[expose] public section

noncomputable section

open GeneralLinearCoordinateRing

open scoped TensorProduct

universe u

namespace SpecialLinearCoordinateRing

variable (K : Type u) [CommRing K] (n : Type u) [Fintype n] [DecidableEq n]

/-- An entry of the determinant-one universal matrix. -/
def entry (i j : n) : CoordinateRing K n := quotient K n (matrix K n i j)

end SpecialLinearCoordinateRing
end
end
