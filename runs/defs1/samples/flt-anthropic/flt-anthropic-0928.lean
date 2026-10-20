set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace AlgebraicGeometry

namespace DescentAction

section repAct

variable {S S' : Scheme.{u}} (s : S' ⟶ S) (G : (Over S)ᵒᵖ ⥤ Type (u + 1)) {X' : Scheme.{u}} (x' : X' ⟶ S')
  (hX' : ((Over.map s).op ⋙ G).RepresentableBy (Over.mk x'))

noncomputable def repAct : pullback (x' ≫ s) s ⟶ X' := (repActOver s G x' hX').left

end repAct
end DescentAction
end AlgebraicGeometry
