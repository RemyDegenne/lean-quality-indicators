namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3_of_oneComplex_weightOneLevi

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse

open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion

open LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction LanglandsTunnell.CubicLambda MeasureTheory

open scoped nonZeroDivisors

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

section

open Complex

namespace DualPressAux

lemma Gammaℝ_two_mul (t : ℂ) : Gammaℝ (2 * t) = (1 / 2 : ℂ) * (2 : ℂ) ^ t * Gammaℂ t := by
  unfold Gammaℝ
  rw [Gammaℂ_def, show (-(2 * t) / 2) = -t by ring, show (2 * t / 2) = t by ring,
    show (2 * (Real.pi : ℂ)) = ((2 : ℝ) : ℂ) * ((Real.pi : ℝ) : ℂ) by push_cast; ring,
    Complex.mul_cpow_ofReal_nonneg (by norm_num) Real.pi_pos.le (-t)]
  push_cast
  have h2 : ((2 : ℂ)) ^ t * (2 : ℂ) ^ (-t) = 1 := by
    rw [← Complex.cpow_add _ _ two_ne_zero, add_neg_cancel, Complex.cpow_zero]
  calc ((Real.pi : ℂ)) ^ (-t) * Complex.Gamma t
      = ((2 : ℂ) ^ t * (2 : ℂ) ^ (-t)) * ((Real.pi : ℂ)) ^ (-t) * Complex.Gamma t := by rw [h2, one_mul]
    _ = _ := by ring

end DualPressAux
end
end P2MW.S_LanglandsTunnell_RankinSelberg_exists_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3_of_oneComplex_weightOneLevi
