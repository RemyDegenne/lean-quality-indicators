@[expose] public section

noncomputable section

open CategoryTheory GeneralLinearCoordinateRing DiagonalCoordinateRing

open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (n : Type u) [Fintype n] [DecidableEq n]

theorem multiplicativeGroupHomUnits_mul (X : Over (Spec (.of K)))
    (f g : X ⟶ (multiplicativeGroupScheme K).X) :
    multiplicativeGroupHomUnits K X (f * g) =
      multiplicativeGroupHomUnits K X f * multiplicativeGroupHomUnits K X g := by
  apply (multiplicativeGroupHomUnits K X).symm.injective
  rw [Equiv.symm_apply_apply, multiplicativeGroupHomUnits_symm_mul,
    Equiv.symm_apply_apply, Equiv.symm_apply_apply]

end AlgebraicGeometry
end
end
