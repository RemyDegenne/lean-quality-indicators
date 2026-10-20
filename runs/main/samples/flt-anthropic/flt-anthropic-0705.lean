namespace P2MW.S_AutomorphicForm_LocalWeightedOrbital_eq_mul_splitOrbital_of_isOrbitalIntegral_diagUnits2

attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain TopologicalSpace Filter

open scoped Topology NNReal ENNReal Pointwise

noncomputable section

namespace C7Iwasawa

section Centralizer

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

open AutomorphicForm

attribute [local instance] t2Space_GL secondCountableTopology_GL locallyCompactSpace_localGL
  AutomorphicForm.localGLBorel AutomorphicForm.borelSpace_localGLBorel AutomorphicForm.isHaarMeasure_localHaar
  AutomorphicForm.localCentralizerBorel

attribute [local instance] locallyCompactSpace_localCentralizer borelSpace_localCentralizer
  secondCountableTopology_localCentralizer

theorem centralizerUnits_eq_preimage (γ : GL (Fin 2) (v.adicCompletion K)) :
    centralizerUnits K v γ =
      ((↑) : localCentralizer K v γ → GL (Fin 2) (v.adicCompletion K)) ⁻¹' localIntegralSet K v := rfl

end Centralizer
end C7Iwasawa
end
end P2MW.S_AutomorphicForm_LocalWeightedOrbital_eq_mul_splitOrbital_of_isOrbitalIntegral_diagUnits2
