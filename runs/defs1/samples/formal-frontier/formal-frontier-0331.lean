set_option warningAsError true

@[expose] public section

open CategoryTheory TopologicalSpace

namespace RingedSpaces.Modules.RingedSpacePushforward

universe u

variable {X Y : AlgebraicGeometry.RingedSpace.{u, u}} (f : X ⟶ Y)

/-- The inverse-image coefficient map for the original full ringed-space morphism. -/
noncomputable def ringSheafMap :
    SheafInverseImage.targetRing f.hom.base Y.sheaf ⟶ ringSheaf X :=
  (SheafInverseImage.sheafForget X.carrier).map
    (AlgebraicGeometry.RingedSpace.inverseImageMap f)

end RingedSpaces.Modules.RingedSpacePushforward
end
