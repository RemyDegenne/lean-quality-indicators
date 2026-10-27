namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_linearMap_stabilised_jacquetIntegral_principalSeries2

attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction AutomorphicForm Filter Topology

open scoped Topology

noncomputable section

namespace LTJacquetFunctional

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)

local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))

attribute [local instance] LanglandsTunnell.TateLocal.localBorel

attribute [local instance] LanglandsTunnell.TateLocal.borelSpace_localBorel

def T (w₀ : G) (θ : AddChar F ℂ) (ν : Measure F) (f : G → ℂ) (g : G) (M : ℤ) : ℂ :=
  ∫ y in ball p M, f (w₀ * unipotentGL2 y * g) * θ y ∂ν

end LTJacquetFunctional
end
end P2MW.S_LanglandsTunnell_CubicInduction_exists_linearMap_stabilised_jacquetIntegral_principalSeries2
