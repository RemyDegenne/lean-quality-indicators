@[expose] public section

open CategoryTheory Limits Opposite TopologicalSpace

namespace RingedSpaces.Modules.SheafInverseImage

universe v

variable {X Y : TopCat.{v}} (f : X ⟶ Y)

/-- Ring sheafification of the neighborhood-colimit presheaf. -/
noncomputable abbrev sheafifiedRing (S : Y.Sheaf CommRingCat.{v}) :=
  RingedSpaces.Modules.PresheafInverseImage.inverseImageSheafRing f (sourceRing S).obj

end RingedSpaces.Modules.SheafInverseImage
end
