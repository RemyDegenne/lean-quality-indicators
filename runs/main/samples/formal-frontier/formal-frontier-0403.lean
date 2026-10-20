@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory

open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (n : Type u) [Fintype n] [LinearOrder n]

variable (R : Type u) [CommRing R] [Algebra K R]

theorem upperTriangularDiagonalSection_point (s : Matrix.DiagonalGroup n R) :
    diagonalGroupMulEquivPoints K n R s ≫
      (upperTriangularDiagonalSection K n).hom.hom =
        upperTriangularGroupMulEquivPoints K n R
          (Matrix.UpperTriangularGroup.diagonalSection s) := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, diagonalGroupMulEquivPoints_apply_left,
    upperTriangularDiagonalSection_left, upperTriangularGroupMulEquivPoints_apply_left]
  change Spec.map (CommRingCat.ofHom (diagonalFromGL K n R s).toRingHom) ≫
    Spec.map (CommRingCat.ofHom
      (upperTriangularDiagonalSectionCoordinateMap K n).toRingHom) =
      Spec.map (CommRingCat.ofHom (upperTriangularFromGL K n R
        (Matrix.UpperTriangularGroup.diagonalSection s)).toRingHom)
  rw [← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom
    ((diagonalFromGL K n R s).comp
      (upperTriangularDiagonalSectionCoordinateMap K n)).toRingHom) = _
  rw [upperTriangularDiagonalSectionCoordinateMap_point]

end AlgebraicGeometry
end
end
