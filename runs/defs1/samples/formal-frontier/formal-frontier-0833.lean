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

/-- The native determinant-one diagonal conjugate. -/
def generalLinearDiagonalConjSL (pivot : n) (unit : Rˣ)
    (matrix : Matrix.SpecialLinearGroup n R) : Matrix.SpecialLinearGroup n R := by
  let diagonal := generalLinearDiagonalHom n pivot unit
  let conjugate := diagonal * Matrix.SpecialLinearGroup.toGL matrix * diagonal⁻¹
  have hdet : Matrix.GeneralLinearGroup.det conjugate = 1 := by
    simp [conjugate, diagonal]
  exact ⟨(conjugate : Matrix n n R), congrArg Units.val hdet⟩

end AlgebraicGeometry
end
end
