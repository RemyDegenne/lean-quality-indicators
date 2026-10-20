@[expose] public section

open CategoryTheory Limits Opposite TopologicalSpace

namespace RingedSpaces.Modules.SheafInverseImage

universe v

variable {X Y : TopCat.{v}} (f : X ⟶ Y)

/-- The ring sheafification unit used for the presheaf adjunction. -/
noncomputable abbrev coefficientSheafUnit (S : Y.Sheaf CommRingCat.{v}) :=
  toSheafify (Opens.grothendieckTopology X) (pointwiseRing f S)

end RingedSpaces.Modules.SheafInverseImage
end
