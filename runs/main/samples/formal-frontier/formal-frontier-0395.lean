public section

noncomputable section

open CategoryTheory GeneralLinearCoordinateRing

open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (n : Type u) [Fintype n] [DecidableEq n]

@[simp] theorem generalLinearDiagonalUnit_apply {R : Type u} [CommRing R]
    (pivot : n) (unit : Rˣ) (i j : n) :
    generalLinearDiagonalUnit n pivot unit i j =
      if i = j then (if i = pivot then (unit : R) else 1) else 0 := rfl

end AlgebraicGeometry
end
end
