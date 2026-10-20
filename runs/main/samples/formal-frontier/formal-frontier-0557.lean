@[expose] public section

noncomputable section

open CategoryTheory GeneralLinearCoordinateRing SpecialLinearCoordinateRing

open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (n : Type u) [Fintype n] [DecidableEq n]

variable (R : Type u) [CommRing R] [Algebra K R]

theorem specialLinearFromSL_comp_quotient (s : Matrix.SpecialLinearGroup n R) :
    (specialLinearFromSL K n R s).comp (quotient K n) =
      evaluate (K := K) (Matrix.SpecialLinearGroup.toGL s) := by
  exact Ideal.Quotient.liftₐ_comp _ _ _

end AlgebraicGeometry
end
end
