@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Category CategoryTheory.Functor TopCat TopologicalSpace

namespace AlgebraicGeometry.RingedSpace

variable (Y : RingedSpace.{u, u}) {T : TopCat.{u}} (g : T ⟶ Y.carrier)

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

theorem inverseImageMap_unit_app (U : (Opens Y.carrier)ᵒᵖ) :
    (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.hom.base).unit.app
        Y.sheaf ≫
      (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).map (inverseImageMap f)).hom).app U =
      f.hom.c.app U :=
  congrArg (fun α => α.app U) (inverseImageMap_unit_hom f)

end AlgebraicGeometry.RingedSpace
end
end
