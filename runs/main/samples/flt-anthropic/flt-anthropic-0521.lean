namespace P2MW.S_LanglandsTunnell_Converse_prod_twistedGammaR_mul_prod_twistedGammaC_archOfParam_eq_archFactor_mul_of_principal

set_option autoImplicit false

open NumberField LanglandsTunnell LanglandsTunnell.Converse Complex

namespace TwistedGammaPress

variable {K : Type} [Field K]

variable (K) [NumberField K]

theorem archFactor_principal_twist (ν₁ ν₂ u : ℂ) (a₁ a₂ c : ZMod 2) (s : ℂ) :
    ((RealArchParam.principal ν₁ a₁ ν₂ a₂).twist u c).archFactor s =
      Gammaℝ (s + (ν₁ + u + signShift (a₁ + c))) * Gammaℝ (s + (ν₂ + u + signShift (a₂ + c))) := by
  simp [RealArchParam.twist, RealArchParam.archFactor, RealArchParam.gammaR, RealArchParam.gammaC]

end TwistedGammaPress
end P2MW.S_LanglandsTunnell_Converse_prod_twistedGammaR_mul_prod_twistedGammaC_archOfParam_eq_archFactor_mul_of_principal
