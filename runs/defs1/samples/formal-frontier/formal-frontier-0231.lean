public section

set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj

open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (n : Type u) [Fintype n] [DecidableEq n]

variable {R : Type u} [CommRing R]

/-- The pivot entry of the diagonal, valued in units before coercion. -/
@[expose] def generalLinearConjDiagonalUnit (pivot : n) (unit : Rˣ) (index : n) : Rˣ :=
  if index = pivot then unit else 1

end AlgebraicGeometry
end
end
