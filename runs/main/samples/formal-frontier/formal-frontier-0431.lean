@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory

open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (n : Type u) [Fintype n] [LinearOrder n]

theorem upperTriangularDiagonalSquare_commutes :
    CommRingCat.ofHom (upperTriangularDiagonalCoordinateMap K n).toRingHom ≫
      CommRingCat.ofHom (upperTriangularUnitriangularCoordinateMap K n).toRingHom =
    CommRingCat.ofHom
        (Bialgebra.counitAlgHom K (DiagonalCoordinateRing.CoordinateRing K n)).toRingHom ≫
      CommRingCat.ofHom
        (algebraMap K (UnitriangularCoordinateRing.CoordinateRing K n)) := by
  apply CommRingCat.hom_ext
  exact congrArg AlgHom.toRingHom (upperTriangularDiagonalSquare_alg K n)

end AlgebraicGeometry
end
end
