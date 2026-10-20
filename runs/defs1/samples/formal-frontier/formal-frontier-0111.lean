@[expose] public section

open CategoryTheory Limits Opposite TopologicalSpace

namespace RingedSpaces.Modules.SheafInverseImage

universe v

variable {X Y : TopCat.{v}} (f : X ⟶ Y)

/-- The actual commutative-ring inverse-image unit, forgotten to ring sheaves. -/
noncomputable def actualUnit (S : Y.Sheaf CommRingCat.{v}) :
    sourceRing S ⟶ (TopCat.Sheaf.pushforward RingCat.{v} f).obj (targetRing f S) :=
  (sheafForget Y).map
    ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{v} f).unit.app S)

end RingedSpaces.Modules.SheafInverseImage
end
