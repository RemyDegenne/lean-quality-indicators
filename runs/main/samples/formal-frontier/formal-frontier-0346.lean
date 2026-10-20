@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory

open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (n : Type u) [Fintype n] [LinearOrder n]

theorem upperTriangularDiagonalSquare_isPullback :
    IsPullback (unitriangularToUpperTriangular K n).hom.hom.left
      (unitriangularGroupUnderlyingScheme K n).hom
      (upperTriangularDiagonalProjection K n).hom.hom.left
      η[diagonalGroupUnderlyingScheme K n].left := by
  change IsPullback
    (Spec.map (CommRingCat.ofHom
      (upperTriangularUnitriangularCoordinateMap K n).toRingHom))
    (Spec.map (CommRingCat.ofHom
      (algebraMap K (UnitriangularCoordinateRing.CoordinateRing K n))))
    (Spec.map (CommRingCat.ofHom
      (upperTriangularDiagonalCoordinateMap K n).toRingHom))
    (Spec.map (CommRingCat.ofHom
      (Bialgebra.counitAlgHom K (DiagonalCoordinateRing.CoordinateRing K n)).toRingHom))
  exact isPullback_SpecMap_of_isPushout _ _ _ _
    (upperTriangularDiagonalSquare_isPushout K n)

end AlgebraicGeometry
end
end
