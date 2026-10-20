@[expose] public section

noncomputable section

open CategoryTheory GeneralLinearCoordinateRing DiagonalCoordinateRing

open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (n : Type u) [Fintype n] [DecidableEq n]

@[simp]
theorem multiplicativeGroupHomUnits_one (X : Over (Spec (.of K))) :
    multiplicativeGroupHomUnits K X (1 : X ⟶ (multiplicativeGroupScheme K).X) = 1 := by
  have h : multiplicativeGroupHomUnits K X 1 * multiplicativeGroupHomUnits K X 1 =
      multiplicativeGroupHomUnits K X 1 := by
    simpa only [one_mul] using
      (multiplicativeGroupHomUnits_mul K X (1 : X ⟶ (multiplicativeGroupScheme K).X) 1).symm
  exact mul_eq_left.mp h

end AlgebraicGeometry
end
end
