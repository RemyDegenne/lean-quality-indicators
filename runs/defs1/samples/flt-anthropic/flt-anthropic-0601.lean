namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_rsFinIntegral_indicator_purified_eq_mul_sum_prod_rsLocalIntegral

attribute [-instance] instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse

open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion

p2m_open

open scoped nonZeroDivisors

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open UnramifiedWhittaker NumberField.AdelicLevel NumberField.TateGlobal LanglandsTunnell.TateLocal

noncomputable section

namespace Ws23CutEval

open UnramifiedWhittaker NumberField.AdelicLevel NumberField.TateGlobal LanglandsTunnell.TateLocal

variable (v : HeightOneSpectrum (𝓞 ℚ))

section AdelicGen

open IsDedekindDomain NumberField Matrix AutomorphicForm

p2m_open

open NumberField.AdelicLevel AdelicDock UnramifiedWhittaker

open Ws23CutEval.TabF

def finWgen (Wl : (v : HeightOneSpectrum (𝓞 ℚ)) → LocalGL3 v → ℂ) (kf : AdelicGL 3 (𝓞 ℚ) ℚ) (g : G2) : ℂ :=
  ∏ᶠ v, Wl v (componentAt3 (𝓞 ℚ) ℚ v (iota (𝓞 ℚ) ℚ g) * componentAt3 (𝓞 ℚ) ℚ v kf)

end AdelicGen
end Ws23CutEval
end
end P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_rsFinIntegral_indicator_purified_eq_mul_sum_prod_rsLocalIntegral
