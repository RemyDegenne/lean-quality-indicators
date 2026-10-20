set_option maxRecDepth 2048

set_option backward.isDefEq.respectTransparency false

set_option warningAsError true

@[expose] public section

namespace RingedSpaces.Modules.BaseChange

open CategoryTheory CategoryTheory.Functor TopologicalSpace PullbackCoherence

universe u

variable {W X Y Z : AlgebraicGeometry.RingedSpace.{u, u}}

theorem pushPull_naturality (bottom : W ⟶ X) (left : W ⟶ Y)
    (top : X ⟶ Z) (right : Y ⟶ Z) (commutes : bottom ≫ top = left ≫ right)
    {M N : ModuleSheaves X} (map : M ⟶ N) :
    (R top ⋙ L right).map map ≫ (pushPull bottom left top right commutes).app N =
      (pushPull bottom left top right commutes).app M ≫ (L bottom ⋙ R left).map map :=
  (pushPull bottom left top right commutes).naturality map

end RingedSpaces.Modules.BaseChange
end
