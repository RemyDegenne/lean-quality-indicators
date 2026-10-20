@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory UnitriangularStageCoordinateRing

open scoped Classical

namespace AlgebraicGeometry

variable (K : Type) [CommRing K] (n r : ℕ)

theorem unitriangularStageCoordinateMap_underlying_affineSpace (hr : 1 ≤ r) :
    (unitriangularStageUnderlyingAffineSpaceIso K n r).inv ≫
        (unitriangularStageCoordinateMap K n r hr).hom.hom ≫
        (additiveGroupProductUnderlyingAffineSpaceIso K
          (Matrix.UnitriangularGroup.superdiagonalIndex n r)).hom =
      (additiveGroupAffineProductSpecToSpaceIso K (SurvivingPair n r)).symm.hom ≫
        stageProductSpecRename K n r hr ≫
        (additiveGroupAffineProductSpecToSpaceIso K
          (Matrix.UnitriangularGroup.superdiagonalIndex n r)).hom := by
  rw [additiveGroupProductUnderlyingAffineSpaceIso, Iso.trans_hom]
  calc
    _ = (unitriangularStageUnderlyingAffineSpaceIso K n r).inv ≫
        (((unitriangularStageCoordinateMap K n r hr).hom.hom ≫
          (additiveGroupProductUnderlyingSpecIso K
            (Matrix.UnitriangularGroup.superdiagonalIndex n r)).hom) ≫
          (additiveGroupAffineProductSpecToSpaceIso K
            (Matrix.UnitriangularGroup.superdiagonalIndex n r)).hom) := by
              simp only [Category.assoc]
    _ = (unitriangularStageUnderlyingAffineSpaceIso K n r).inv ≫
        (((unitriangularStageUnderlyingSpecIso K n r).hom ≫
          stageProductSpecRename K n r hr) ≫
          (additiveGroupAffineProductSpecToSpaceIso K
            (Matrix.UnitriangularGroup.superdiagonalIndex n r)).hom) := by
              rw [unitriangularStageCoordinateMap_underlying_spec]
    _ = _ := by
      rw [unitriangularStageUnderlyingSpecIso, Iso.trans_hom]
      simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp, Iso.symm_hom]

end AlgebraicGeometry
end
end
