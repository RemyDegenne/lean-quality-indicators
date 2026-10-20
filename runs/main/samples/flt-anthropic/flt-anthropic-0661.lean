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

variable {K v}

variable (K v)

theorem measurableSet_setOf_mul_mem (γ : GL (Fin 2) (v.adicCompletion K)) (x : GL (Fin 2) (v.adicCompletion K))
    (C : ℝ) :
    MeasurableSet {t : localCentralizer K v γ | (t : GL (Fin 2) (v.adicCompletion K)) * x ∈ unipKSet K v C} :=
  ((isClosed_unipKSet K v C).preimage (continuous_subtype_val.mul continuous_const)).measurableSet

end Centralizer
end C7Iwasawa
end
end P2MW.S_AutomorphicForm_LocalWeightedOrbital_eq_mul_splitOrbital_of_isOrbitalIntegral_diagUnits2
