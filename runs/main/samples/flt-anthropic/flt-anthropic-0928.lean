namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_reducesToOrigin_mul_originParam_eq_formalGroupLawFixed

set_option autoImplicit false

p2m_open

attribute [local instance] MvPolynomial.gradedAlgebra

attribute [local instance] WeierstrassProjModel.kw_pbac_awayAlgebra

namespace WeierstrassCurve

namespace DrinfeldGlobal

namespace UnivFormalAdd

p2m_open

open MvPolynomial HomogeneousLocalization NeronModelInfra

section Formal

variable {A : Type} [CommRing A] (W : WeierstrassCurve A)

theorem constantCoeff_fgGenW {σ : Type} (z : MvPowerSeries σ A) (hz : MvPowerSeries.constantCoeff z = 0) :
    MvPowerSeries.constantCoeff (W.fgGenW z) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero hz _ W.constantCoeff_formalW

end Formal
end UnivFormalAdd
end DrinfeldGlobal
end WeierstrassCurve
end P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_reducesToOrigin_mul_originParam_eq_formalGroupLawFixed
