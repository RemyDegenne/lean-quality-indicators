@[expose] public section

noncomputable section

open CategoryTheory GeneralLinearCoordinateRing UnitriangularCoordinateRing

open scoped CategoryTheory MonObj TensorProduct

namespace AlgebraicGeometry

variable (K : Type) [CommRing K] (n r : ℕ)

open UnitriangularStageCoordinateRing

set_option backward.isDefEq.respectTransparency false

variable (R : Type) [CommRing R] [Algebra K R]

theorem unitriangularStageInclusion_point
    (s : Matrix.UnitriangularGroup.superdiagonalSubgroup n R r) :
    unitriangularStagePointMulEquiv K n r R s ≫
        (unitriangularStageInclusion K n r).hom.hom =
      unitriangularGroupMulEquivPoints K (Fin n) R s.1 := by
  apply Over.OverMorphism.ext
  change ((unitriangularStagePointMulEquiv K n r R s).left ≫
    (unitriangularStageInclusion K n r).hom.hom.left) =
      (unitriangularGroupMulEquivPoints K (Fin n) R s.1).left
  rw [unitriangularStagePointMulEquiv_apply_left,
    unitriangularStageInclusion_left, unitriangularGroupMulEquivPoints_apply_left,
    ← Spec.map_comp]
  congr 1

end AlgebraicGeometry
end
end
