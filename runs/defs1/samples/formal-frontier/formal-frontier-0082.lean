@[expose] public section

noncomputable section

open GeneralLinearCoordinateRing

open scoped TensorProduct

universe u

namespace UnitriangularCoordinateRing

variable (K : Type u) [CommRing K] (ι : Type u) [Fintype ι] [LinearOrder ι]

/-- The universal matrix over the quotient, as an invertible native matrix. -/
def universal : Matrix.GeneralLinearGroup ι (CoordinateRing K ι) :=
  Matrix.GeneralLinearGroup.map (quotient K ι).toRingHom
    (GeneralLinearCoordinateRing.universal K ι)

end UnitriangularCoordinateRing
end
end
