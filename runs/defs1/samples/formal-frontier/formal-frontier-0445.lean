@[expose] public section

noncomputable section

open CategoryTheory GeneralLinearCoordinateRing UnitriangularCoordinateRing

open scoped CategoryTheory MonObj TensorProduct

namespace AlgebraicGeometry

variable (K : Type) [CommRing K] (n r : ℕ)

open UnitriangularStageCoordinateRing

set_option backward.isDefEq.respectTransparency false

variable (R : Type) [CommRing R] [Algebra K R]

/-- Underlying successor inclusion on the matrix groups. -/
def unitriangularStagePointSuccessor
    (s : Matrix.UnitriangularGroup.superdiagonalSubgroup n R (r + 1)) :
    Matrix.UnitriangularGroup.superdiagonalSubgroup n R r :=
  ⟨s.1, (Matrix.UnitriangularGroup.superdiagonalSubgroup_succ_le n R r) s.2⟩

end AlgebraicGeometry
end
end
