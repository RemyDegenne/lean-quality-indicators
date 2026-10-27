set_option autoImplicit false

set_option maxHeartbeats 800000

set_option synthInstance.maxHeartbeats 200000

noncomputable section

namespace FppfRepresentableGroupSchemeSheaf

open CategoryTheory AlgebraicGeometry Limits Opposite MonoidalCategory CartesianMonoidalCategory

open scoped CategoryTheory.MonObj

universe w v₁ u₁ u

section GroupSchemeOverBase

variable (S : Scheme.{u})

variable (G : Over S) [GrpObj G]

variable [IsCommMonObj G]

def yonedaCommGrpObjOverRepresentableBy :
    (yonedaCommGrpObjOver S G ⋙ forget CommGrpCat).RepresentableBy G where
  homEquiv := Equiv.refl _
  homEquiv_comp _ _ := rfl

end GroupSchemeOverBase
end FppfRepresentableGroupSchemeSheaf
end
