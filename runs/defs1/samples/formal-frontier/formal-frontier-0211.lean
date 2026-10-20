@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory

open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (n : Type u) [Fintype n] [LinearOrder n]

/-- The unitriangular quotient is a morphism of Hopf coordinate algebras. -/
def upperTriangularUnitriangularBialgHom :
    UpperTriangularCoordinateRing.CoordinateRing K n →ₐc[K]
      UnitriangularCoordinateRing.CoordinateRing K n :=
  bialgHomOfCompQuotient K n (unitriangularQuotientBialgHom K n)
    (upperTriangularUnitriangularCoordinateMap K n)
    (upperTriangularUnitriangularCoordinateMap_comp_quotient K n)

end AlgebraicGeometry
end
end
