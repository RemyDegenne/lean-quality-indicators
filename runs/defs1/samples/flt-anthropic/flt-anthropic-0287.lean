namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_group_forall_nonempty_pointsEquiv_of_isFinite_of_etale

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

open scoped TensorProduct

universe u

namespace LevelFibreBody

noncomputable section

section Points

abbrev ΓC (C : Scheme.{u}) : CommRingCat.{u} := Γ(C, ⊤)

end Points
end
end LevelFibreBody
end P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_group_forall_nonempty_pointsEquiv_of_isFinite_of_etale
