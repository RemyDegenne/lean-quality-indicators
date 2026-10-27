@[expose] public section

noncomputable section

open CategoryTheory GeneralLinearCoordinateRing DiagonalCoordinateRing

open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (n : Type u) [Fintype n] [DecidableEq n]

/-- Pullback of the `j`-th Laurent coordinate along the diagonal projection. -/
def diagonalGroupProjectionCoordinateMap (j : n) :
    multiplicativeGroupCoordinateRing K →ₐ[K] DiagonalCoordinateRing.CoordinateRing K n :=
  (multiplicativeGroupMulEquivAlgHom K (DiagonalCoordinateRing.CoordinateRing K n)
    (Matrix.DiagonalGroup.unitsEquiv (universal K n) j)).ofConv

end AlgebraicGeometry
end
end
