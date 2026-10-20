namespace P2MW.S_AutomorphicForm_GL2Real_withDensity_volume_iwasawaBox_eq_two_mul_pi

set_option autoImplicit false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

set_option linter.unusedSimpArgs false

open MeasureTheory Set AutomorphicForm

open scoped ENNReal Real

noncomputable section

namespace P2mIwasawaBox

theorem lintegral_G : ∫⁻ p, G p ∂(volume : Measure P) = ENNReal.ofReal (2 * Real.pi) := by
  rw [Measure.volume_eq_prod, lintegral_prod_symm _ measurable_G.aemeasurable]
  simp_rw [lintegral_G_section]
  exact lintegral_annulus

end P2mIwasawaBox
end
end P2MW.S_AutomorphicForm_GL2Real_withDensity_volume_iwasawaBox_eq_two_mul_pi
