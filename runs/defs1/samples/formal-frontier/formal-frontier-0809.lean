@[expose] public section

noncomputable section

open GeneralLinearCoordinateRing

open scoped TensorProduct

universe u

namespace UnitriangularCoordinateRing

variable (K : Type u) [CommRing K] (ι : Type u) [Fintype ι] [LinearOrder ι]

variable {K ι}

variable (K ι)

/-- The independent coordinates are precisely the strictly upper pairs. -/
abbrev StrictUpperPair := { p : ι × ι // p.1 < p.2 }

end UnitriangularCoordinateRing
end
end
