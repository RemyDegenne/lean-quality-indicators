@[expose] public section

noncomputable section

open GeneralLinearCoordinateRing UnitriangularCoordinateRing

open scoped TensorProduct

namespace UnitriangularStageCoordinateRing

variable (K : Type) [CommRing K] (n r : ℕ)

noncomputable local instance : Coalgebra K (CoordinateRing K n r) :=
  (inferInstance : Bialgebra K (CoordinateRing K n r)).toCoalgebra

noncomputable local instance : CoalgebraStruct K (CoordinateRing K n r) :=
  (inferInstance : Coalgebra K (CoordinateRing K n r)).toCoalgebraStruct

/-- The universal entry on the `r`-th superdiagonal of the stage algebra.
Milne, *Algebraic Groups* (2017), §6.49 uses one-entry additive
coordinates in the finer field-case filtration. -/
def coordinate (ij : Matrix.UnitriangularGroup.superdiagonalIndex n r) :
    CoordinateRing K n r :=
  quotient K n r (entry K n ij.1.1 ij.1.2)

end UnitriangularStageCoordinateRing
end
end
