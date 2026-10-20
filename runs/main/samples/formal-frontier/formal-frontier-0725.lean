set_option warningAsError true

@[expose] public section

open CategoryTheory TopologicalSpace

namespace RingedSpaces.Modules.RingedSpacePushforward

universe u

variable {X Y : AlgebraicGeometry.RingedSpace.{u, u}} (f : X ⟶ Y)

set_option backward.isDefEq.respectTransparency false

theorem restrictPushforwardIso_inverseLaws (M : SheafOfModules.{u} (ringSheaf X)) :
    (restrictPushforwardIso f).hom.app M ≫ (restrictPushforwardIso f).inv.app M =
        𝟙 _ ∧
      (restrictPushforwardIso f).inv.app M ≫ (restrictPushforwardIso f).hom.app M =
        𝟙 _ :=
  ⟨(restrictPushforwardIso f).hom_inv_id_app M,
    (restrictPushforwardIso f).inv_hom_id_app M⟩

end RingedSpaces.Modules.RingedSpacePushforward
end
