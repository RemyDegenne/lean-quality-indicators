@[expose] public section

noncomputable section

open GeneralLinearCoordinateRing

open scoped TensorProduct

universe u

namespace UnitriangularCoordinateRing

variable (K : Type u) [CommRing K] (ι : Type u) [Fintype ι] [LinearOrder ι]

/-- Coordinate algebra of the upper-unitriangular group. -/
abbrev CoordinateRing := GeneralLinearCoordinateRing.CoordinateRing K ι ⧸ ideal K ι

end UnitriangularCoordinateRing
end
end
