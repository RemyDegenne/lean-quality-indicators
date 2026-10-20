namespace P2MW.S_LanglandsTunnell_Converse_exists_forall_integrable_dualQuadruple_and_torusTriple_minor_of_mulConvGaussian_sheets

set_option autoImplicit false

open NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse MeasureTheory

open Set Real

noncomputable section

namespace K7RB3b

open LanglandsTunnell.Converse.ArchR K7RA5 K7RA5b K7RA5c

local notation "μ3" => Measure.prod (volume : Measure ℝ) (Measure.prod (volume : Measure ℝ) (Measure.restrict (volume : Measure ℝ) (Ioi (0:ℝ))))

theorem integrable_triple' {φ : ℝ → ℝ} (hφ : Integrable φ) {a : ℝ} (ha : a ≠ 0) {b g : ℝ} (hb : b < -1) (hg : g < -1) :
    Integrable (fun q : ℝ × ℝ × ℝ =>
      φ q.1 * ((|q.2.1| ^ b * rexp (-(π * a ^ 2 / q.2.1 ^ 2))) * (q.2.2 ^ g * rexp (-(π * a ^ 2 / q.2.2 ^ 2))))) μ3 :=
  hφ.mul_prod ((integrable_Ya ha hb).mul_prod (integrableOn_Za ha hg))

end K7RB3b
end
end P2MW.S_LanglandsTunnell_Converse_exists_forall_integrable_dualQuadruple_and_torusTriple_minor_of_mulConvGaussian_sheets
