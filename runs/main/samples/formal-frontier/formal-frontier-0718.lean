@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Topology

namespace AlgebraicGeometry.RingedSpace

universe u

namespace OpenCover

variable {X : RingedSpace.{u, u}} (C : OpenCover X)

local notation "topGlueData" =>
  C.glueData.toPresheafedSpaceGlueData.toTopGlueData.toGlueData

theorem existsUnique_gluing_of_intersection {Y : RingedSpace.{u, u}}
    (f : ∀ i, C.obj i ⟶ Y)
    (hf : ∀ i j, restrictMap (C.U i ⊓ C.U j) (C.U i) inf_le_left ≫ f i =
      restrictMap (C.U i ⊓ C.U j) (C.U j) inf_le_right ≫ f j) :
    ∃! g : X ⟶ Y, ∀ i, C.ι i ≫ g = f i :=
  C.existsUnique_gluing f ((C.pullback_compatibility_iff_intersection f).mpr hf)

end OpenCover
end AlgebraicGeometry.RingedSpace
end
