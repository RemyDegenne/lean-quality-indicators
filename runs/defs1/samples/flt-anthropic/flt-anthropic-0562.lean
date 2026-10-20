namespace P2MW.S_LanglandsTunnell_Converse_exists_forall_integrable_thetaFree_iwasawaIntegrand_blockHarmonic_of_mulConvGaussian_sheets

set_option autoImplicit false

open NumberField LanglandsTunnell LanglandsTunnell.Converse MeasureTheory

open Set Real

noncomputable section

namespace K7RA5

local notation "μ0" => Measure.restrict (volume : Measure ℝ) (Ioi (0:ℝ))

def G (p q : ℂ) (y : ℝ) : ℂ := (4 : ℂ) * ∫ r in Ioi (0:ℝ), prof p q y r

end K7RA5
end
end P2MW.S_LanglandsTunnell_Converse_exists_forall_integrable_thetaFree_iwasawaIntegrand_blockHarmonic_of_mulConvGaussian_sheets
