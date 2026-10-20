namespace P2MW.S_AlgebraicGeometry_RiemannForm_isLevelPairingValue_of_isLevelPairingValue_pushPt_of_iso_pullback

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RiemannForm

noncomputable section

namespace RFFunct29

namespace Mod

open ConstPullback

variable {k : Type} [Field k]

def D {X Y Z : Scheme.{0}} (u : X ⟶ Y) (v : Y ⟶ Z) (w : X ⟶ Z) (h : u ≫ v = w) :
    Scheme.Modules.pullback v ⋙ Scheme.Modules.pullback u ≅ Scheme.Modules.pullback w :=
  Scheme.Modules.pullbackComp u v ≪≫ Scheme.Modules.pullbackCongr h

end Mod
end RFFunct29
end
end P2MW.S_AlgebraicGeometry_RiemannForm_isLevelPairingValue_of_isLevelPairingValue_pushPt_of_iso_pullback
