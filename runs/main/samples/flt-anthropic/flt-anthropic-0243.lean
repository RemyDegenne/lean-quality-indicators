namespace P2MW.S_LanglandsTunnell_RankinSelberg_dualTorusPair_eq_const_mul_setIntegral_scaledShape_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm AutomorphicForm.WindowedSiegel LanglandsTunnell LanglandsTunnell.Converse

open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion

open LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction LanglandsTunnell.CubicLambda MeasureTheory

open scoped nonZeroDivisors

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

p2m_reactivate

p2m_reactivate

namespace DualB

open DualKit K7Rot

theorem inv_ofReal_cpow {r : ℝ} (hr : 0 < r) (s : ℂ) : (((r⁻¹ : ℝ)) : ℂ) ^ s = ((r : ℝ) : ℂ) ^ (-s) := by
  rw [Complex.ofReal_inv, Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg hr.le]; exact Real.pi_ne_zero.symm),
    Complex.cpow_neg]

end DualB
end P2MW.S_LanglandsTunnell_RankinSelberg_dualTorusPair_eq_const_mul_setIntegral_scaledShape_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3
