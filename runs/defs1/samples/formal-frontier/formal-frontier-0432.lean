@[expose] public section

noncomputable section

open CategoryTheory GeneralLinearCoordinateRing DiagonalCoordinateRing

open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (n : Type u) [Fintype n] [DecidableEq n]

/-- The genuine projection fan in group objects over the base. -/
def diagonalGroupProductFan : Limits.Fan (fun _ : n ↦ multiplicativeGroupScheme K) :=
  Limits.Fan.mk (diagonalGroupScheme K n) (diagonalGroupProjection K n)

end AlgebraicGeometry
end
end
