set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace AlgebraicGeometry

structure DescentAction {S S' : Scheme.{u}} (s : S' ⟶ S) {X' : Scheme.{u}} (x' : X' ⟶ S') where

  act : pullback (x' ≫ s) s ⟶ X'
  act_comp : act ≫ x' = pullback.snd _ _
  unit_act : DescentAction.unitMap s x' ≫ act = 𝟙 X'
  trans : DescentAction.actMap act act_comp ≫ act = DescentAction.proj₁₃ s x' ≫ act

end AlgebraicGeometry
