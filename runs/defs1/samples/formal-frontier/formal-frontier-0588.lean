@[expose] public section

noncomputable section

open GeneralLinearCoordinateRing

open scoped TensorProduct

universe u

namespace UnitriangularCoordinateRing

variable (K : Type u) [CommRing K] (ι : Type u) [Fintype ι] [LinearOrder ι]

/-- The canonical quotient of the published GL coordinate algebra. -/
def quotient : GeneralLinearCoordinateRing.CoordinateRing K ι →ₐ[K] CoordinateRing K ι :=
  Ideal.Quotient.mkₐ K (ideal K ι)

end UnitriangularCoordinateRing
end
end
