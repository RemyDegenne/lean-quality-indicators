set_option maxRecDepth 2048

set_option backward.isDefEq.respectTransparency false

set_option warningAsError true

@[expose] public section

namespace RingedSpaces.Modules.BaseChange

open CategoryTheory CategoryTheory.Functor TopologicalSpace PullbackCoherence

universe u

variable {W X Y Z : AlgebraicGeometry.RingedSpace.{u, u}}

theorem pushforwardSquare_identity_app (top : X ⟶ Z) (M : ModuleSheaves X) :
    (pushforwardSquare (𝟙 X) top top (𝟙 Z) (by simp)).hom.app M ≫
      (pushforwardId Z).hom.app ((R top).obj M) =
        (R top).map ((pushforwardId X).hom.app M) := by
  rw [pushforwardSquare_identity]
  simp

end RingedSpaces.Modules.BaseChange
end
