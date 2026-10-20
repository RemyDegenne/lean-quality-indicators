namespace P2MW.S_LanglandsTunnell_Converse_exists_forall_integrable_thetaFree_iwasawaIntegrand_conjBlock_of_mulConvGaussian_profile

set_option autoImplicit false

open NumberField LanglandsTunnell LanglandsTunnell.Converse MeasureTheory

open Set Real

noncomputable section

namespace K7RA5

local notation "μ0" => Measure.restrict (volume : Measure ℝ) (Ioi (0:ℝ))

theorem integrableOn_cpow_mul_G (p q A : ℂ) {lam : ℝ} (hlam : 0 < lam) (hp : -1 < A.re + p.re) (hq : -1 < A.re + q.re) :
    IntegrableOn (fun t : ℝ => ((t : ℝ) : ℂ) ^ A * G p q (lam * t)) (Ioi 0) := by
  have h := (integrable_Φ p q A hlam hp hq).integral_prod_left
  have h4 := h.const_mul (4 : ℂ)
  refine h4.congr (ae_of_all _ fun t => ?_)
  simp only [G, Φ]
  rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul]
  congr 1; funext r; ring

end K7RA5
end
end P2MW.S_LanglandsTunnell_Converse_exists_forall_integrable_thetaFree_iwasawaIntegrand_conjBlock_of_mulConvGaussian_profile
