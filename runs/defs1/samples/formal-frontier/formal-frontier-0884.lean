@[expose] public section

noncomputable section

open CategoryTheory GeneralLinearCoordinateRing UpperTriangularCoordinateRing

open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (n : Type u) [Fintype n] [LinearOrder n]

variable (R : Type u) [CommRing R] [Algebra K R]

/-- The represented group-valued point functor on commutative `K`-algebras. -/
abbrev upperTriangularGroupPointsFunctor : CommAlgCat K ⥤ GrpCat :=
  (algSpec (.of K)).rightOp ⋙ yonedaGrp.obj (upperTriangularGroupScheme K n)

end AlgebraicGeometry
end
end
