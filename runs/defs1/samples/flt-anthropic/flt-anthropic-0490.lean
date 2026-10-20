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

def fppfOverAbelianSheaf : Sheaf (fppfTopologyOver S) AddCommGrpCat.{u} :=
  ⟨yonedaAddCommGrpObjOver S G, isSheaf_fppfOver_yonedaAddCommGrpObjOver S G⟩

end GroupSchemeOverBase
end FppfRepresentableGroupSchemeSheaf
end
