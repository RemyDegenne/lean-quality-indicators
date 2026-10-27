@[expose] public section

open CategoryTheory Limits Opposite TopologicalSpace

namespace RingedSpaces.Modules.SheafInverseImage

universe v

variable {X Y : TopCat.{v}} (f : X ⟶ Y)

/-- The actual native sheaf-module pushforward, not an abstract right adjoint. -/
noncomputable def pushforwardFunctor (S : Y.Sheaf CommRingCat.{v}) :
    SheafOfModules.{v} (targetRing f S) ⥤ SheafOfModules.{v} (sourceRing S) :=
  SheafOfModules.pushforward (F := Opens.map f) (actualUnit f S)

end RingedSpaces.Modules.SheafInverseImage
end
