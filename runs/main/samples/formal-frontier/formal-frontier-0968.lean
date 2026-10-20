@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Topology

namespace AlgebraicGeometry.RingedSpace

universe u

namespace OpenCover

variable {X : RingedSpace.{u, u}} (C : OpenCover X)

local notation "topGlueData" =>
  C.glueData.toPresheafedSpaceGlueData.toTopGlueData.toGlueData

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
theorem ι_glueMorphisms {Y : RingedSpace.{u, u}} (f : ∀ i, C.obj i ⟶ Y)
    (hf : ∀ i j, pullback.fst (C.ι i) (C.ι j) ≫ f i =
      pullback.snd (C.ι i) (C.ι j) ≫ f j) (i : C.J) :
    C.ι i ≫ C.glueMorphisms f hf = f i := by
  rw [C.glueMorphisms_eq_original]
  have : IsIso C.fromGlued := C.fromGlued_isIso
  rw [← C.gluedι_fromGlued i]
  simp only [Category.assoc, glueMorphismsOriginal, IsIso.hom_inv_id_assoc]
  apply Multicoequalizer.π_desc

end OpenCover
end AlgebraicGeometry.RingedSpace
end
