namespace P2MW.S_AlgebraicGeometry_RiemannForm_isLevelPairingValue_mul_of_isLevelPairingValue_nsmul

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RiemannForm

namespace RFCompatE165

universe u

set_option backward.isDefEq.respectTransparency false

section heart

variable {A : Scheme.{0}}

noncomputable def iota (Mm N W : A ⟶ A) (hW : W = Mm ≫ N) (M : A.Modules) :
    (Scheme.Modules.pullback W).obj M ≅ (Scheme.Modules.pullback Mm).obj ((Scheme.Modules.pullback N).obj M) :=
  (Scheme.Modules.pullbackCongr hW).app M ≪≫ ((Scheme.Modules.pullbackComp Mm N).app M).symm

end heart
end RFCompatE165
end P2MW.S_AlgebraicGeometry_RiemannForm_isLevelPairingValue_mul_of_isLevelPairingValue_nsmul
