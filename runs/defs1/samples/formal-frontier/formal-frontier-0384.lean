@[expose] public section

noncomputable section

open CategoryTheory GeneralLinearCoordinateRing

open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (n : Type u) [Fintype n] [DecidableEq n]

/-- Group-valued affine points of the GL group scheme. -/
abbrev generalLinearGroupPointsFunctor : CommAlgCat K ⥤ GrpCat :=
  (algSpec (.of K)).rightOp ⋙ yonedaGrp.obj (generalLinearGroupScheme K n)

end AlgebraicGeometry
end
end
