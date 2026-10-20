namespace P2MW.S_AlgebraicGeometry_SmallExtension_exists_isPicDeformationCocycle_of_cechTrivialisation

set_option autoImplicit false

p2m_open

universe u

namespace PV1TL

p2m_open

variable {Y : Scheme.{u}}

noncomputable def uASm (W : Y.Opens)
    (E : @Iso ((W : Scheme.{u}).Modules) _ (SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf)
      (SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf)) : Γ(Y, W) :=
  unitAutSection W E

end PV1TL
end P2MW.S_AlgebraicGeometry_SmallExtension_exists_isPicDeformationCocycle_of_cechTrivialisation
