@[expose] public section

open CategoryTheory Limits Opposite TopologicalSpace

open CategoryTheory Limits Opposite TopologicalSpace

namespace RingedSpaces.Modules.SheafInverseImage

universe v

variable {X Y : TopCat.{v}} (f : X ⟶ Y)

/-- Forget commutativity of a sheaf of rings, compatibly with its sheaf condition. -/
abbrev sheafForget (T : TopCat.{v}) :=
  sheafCompose (Opens.grothendieckTopology T) (forget₂ CommRingCat.{v} RingCat.{v})

end RingedSpaces.Modules.SheafInverseImage
end
