namespace P2MW.S_LanglandsTunnell_RankinSelberg_dualTorusPair_eq_const_mul_setIntegral_scaledShape_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm AutomorphicForm.WindowedSiegel LanglandsTunnell LanglandsTunnell.Converse

open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion

open LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction LanglandsTunnell.CubicLambda MeasureTheory

open scoped nonZeroDivisors

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

namespace K7Rot

theorem archWeightOneℝ_rotK (θ : ℝ) :
    (archWeightOneℝ (rotK θ) : ℂ) = Complex.exp (-(θ : ℂ) * Complex.I) := by
  show firstRowℂ (rotGL θ) = _
  apply Complex.ext
  · simp [firstRowℂ, rotM, Complex.exp_re]
  · simp [firstRowℂ, rotM, Complex.exp_im]

end K7Rot
end P2MW.S_LanglandsTunnell_RankinSelberg_dualTorusPair_eq_const_mul_setIntegral_scaledShape_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3
