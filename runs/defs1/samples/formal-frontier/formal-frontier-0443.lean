@[expose] public section

noncomputable section

open GeneralLinearCoordinateRing

open scoped TensorProduct

universe u

namespace UnitriangularCoordinateRing

variable (K : Type u) [CommRing K] (ι : Type u) [Fintype ι] [LinearOrder ι]

/-- Each relation is either a lower entry, a diagonal entry minus one, or zero. -/
def relation (i j : ι) : GeneralLinearCoordinateRing.CoordinateRing K ι :=
  if j < i then matrix K ι i j else if i = j then matrix K ι i j - 1 else 0

end UnitriangularCoordinateRing
end
end
