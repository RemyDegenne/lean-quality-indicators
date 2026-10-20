namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_isZero_exteriorPower_of_isLocallyFreeOfRank

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

universe u

p2m_open

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

namespace AlgebraicGeometry

namespace Scheme

namespace Modules

p2m_open

open TopologicalSpace

variable (X : Scheme.{u}) (n : ℕ)

noncomputable def exteriorPowerFreeIso :
    (exteriorPower X n).obj (SheafOfModules.free.{u} (ULift.{u} (Fin n))) ≅
      SheafOfModules.unit X.ringCatSheaf :=
  (exteriorPower X n).mapIso (freeIsoPiPow X n) ≪≫
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
      (PresheafOfModules.exteriorPowerPiPowIso X.sheaf.obj n) ≪≫
    sheafificationUnitIso X

end Modules
end Scheme
end AlgebraicGeometry
end P2MW.S_AlgebraicGeometry_Scheme_Modules_isZero_exteriorPower_of_isLocallyFreeOfRank
