namespace P2MW.S_LanglandsTunnell_Converse_exists_forall_integrable_postGaussian_torusTriple_conjBlock_of_mulConvGaussian_profile

set_option autoImplicit false

open NumberField LanglandsTunnell LanglandsTunnell.Converse MeasureTheory

open Set Real

noncomputable section

namespace K7RA5

local notation "μ0" => Measure.restrict (volume : Measure ℝ) (Ioi (0:ℝ))

def Φ (p q A : ℂ) (lam : ℝ) (w : ℝ × ℝ) : ℂ := ((w.1 : ℝ) : ℂ) ^ A * prof p q (lam * w.1) w.2

end K7RA5
end
end P2MW.S_LanglandsTunnell_Converse_exists_forall_integrable_postGaussian_torusTriple_conjBlock_of_mulConvGaussian_profile
