public section

noncomputable section

open CategoryTheory GeneralLinearCoordinateRing

open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (n : Type u) [Fintype n] [DecidableEq n]

/-- The invertible Laurent coordinate, represented as a unit. -/
def generalLinearSectionLaurentUnit : (multiplicativeGroupCoordinateRing K)ˣ :=
  (multiplicativeGroupCoordinate_isUnit K).unit

end AlgebraicGeometry
end
end
