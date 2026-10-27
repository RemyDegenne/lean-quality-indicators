set_option maxRecDepth 2048

set_option backward.isDefEq.respectTransparency false

set_option warningAsError true

@[expose] public section

namespace RingedSpaces.Modules.BaseChange

open CategoryTheory CategoryTheory.Functor TopologicalSpace PullbackCoherence

universe u

variable {W X Y Z : AlgebraicGeometry.RingedSpace.{u, u}}

/-- The canonical comparison of direct images around a full commutative square. -/
noncomputable def pushforwardSquare (bottom : W ⟶ X) (left : W ⟶ Y)
    (top : X ⟶ Z) (right : Y ⟶ Z) (commutes : bottom ≫ top = left ≫ right) :
    R bottom ⋙ R top ≅ R left ⋙ R right :=
  pushforwardComp bottom top ≪≫ eqToIso (congrArg R commutes) ≪≫
    (pushforwardComp left right).symm

end RingedSpaces.Modules.BaseChange
end
