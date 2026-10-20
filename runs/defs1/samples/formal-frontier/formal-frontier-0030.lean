@[expose] public section

open CategoryTheory Limits Opposite TopologicalSpace

namespace RingedSpaces.Modules.PresheafInverseImage

universe v

variable {X Y : TopCat.{v}} (f : X ⟶ Y)

/-- Sheafify the ordinary ring presheaf inverse image. -/
noncomputable def inverseImageSheafRing (R : Y.Presheaf RingCat.{v}) :
    X.Sheaf RingCat.{v} :=
  (presheafToSheaf (Opens.grothendieckTopology X) RingCat.{v}).obj
    ((Opens.map f).op.pointwiseLeftKanExtension R)

end RingedSpaces.Modules.PresheafInverseImage
end
