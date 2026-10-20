@[expose] public section

open CategoryTheory Limits Opposite TopologicalSpace

namespace RingedSpaces.Modules.SheafInverseImage

universe v

variable {X Y : TopCat.{v}} (f : X ⟶ Y)

/-- The actual ring comparison needed for the final scalar restriction. -/
noncomputable def ringIso (S : Y.Sheaf CommRingCat.{v}) :
    targetRing f S ≅ sheafifiedRing f S :=
  RingedSpaces.Modules.SheafInverseImage.comparison f S ≪≫
    (RingedSpaces.Modules.PresheafInverseImage.inverseImageSheafRingComparison f (sourceRing S)).symm

end RingedSpaces.Modules.SheafInverseImage
end
