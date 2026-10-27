@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Category CategoryTheory.Functor TopCat TopologicalSpace

namespace AlgebraicGeometry.RingedSpace

variable (Y : RingedSpace.{u, u}) {T : TopCat.{u}} (g : T ⟶ Y.carrier)

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- The adjoint of the full structure-sheaf morphism of `f`, as a map of ring sheaves. -/
def inverseImageMap :
    (inverseImage Y f.hom.base).sheaf ⟶ X.sheaf :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.hom.base).homEquiv
    Y.sheaf X.sheaf).symm ((CategoryTheory.Sheaf.homEquiv).symm f.hom.c)

end AlgebraicGeometry.RingedSpace
end
end
