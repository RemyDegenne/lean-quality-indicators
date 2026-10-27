@[expose] public section

noncomputable section

open GeneralLinearCoordinateRing

open scoped TensorProduct

universe u

namespace UpperTriangularCoordinateRing

variable (K : Type u) [CommRing K] (ι : Type u) [Fintype ι] [LinearOrder ι]

/-- Coordinate algebra of the closed upper-triangular subgroup of GL. -/
abbrev CoordinateRing := GeneralLinearCoordinateRing.CoordinateRing K ι ⧸ ideal K ι

end UpperTriangularCoordinateRing
end
end
