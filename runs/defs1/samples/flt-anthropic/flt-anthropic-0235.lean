namespace P2MW.S_AlgebraicGeometry_RiemannForm_existsUnique_isConstScalar

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RiemannForm Opposite TopologicalSpace

namespace RFConst

variable {X : Scheme.{0}}

def res' (r : Γ(X, ⊤)) (U : X.Opens) : Γ(X, U) := X.presheaf.map (homOfLE (le_top (a := U))).op r

end RFConst
end
end P2MW.S_AlgebraicGeometry_RiemannForm_existsUnique_isConstScalar
