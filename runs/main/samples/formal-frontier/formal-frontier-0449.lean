@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Category CategoryTheory.Functor TopCat TopologicalSpace

namespace AlgebraicGeometry.RingedSpace

variable (Y : RingedSpace.{u, u}) {T : TopCat.{u}} (g : T ⟶ Y.carrier)

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

theorem inverseImageMap_unit :
    (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.hom.base).unit.app
        Y.sheaf ≫
      (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).map (inverseImageMap f) =
      (CategoryTheory.Sheaf.homEquiv).symm f.hom.c := by
  change ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.hom.base).homEquiv
    Y.sheaf X.sheaf) (inverseImageMap f) = (CategoryTheory.Sheaf.homEquiv).symm f.hom.c
  exact Equiv.apply_symm_apply _ _

end AlgebraicGeometry.RingedSpace
end
end
