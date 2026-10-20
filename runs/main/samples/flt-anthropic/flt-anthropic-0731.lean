namespace P2MW.S_AutomorphicForm_integrable_and_differentiableAt_and_continuous_godementSection_of_mem_schwartzBruhat2

attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

open MeasureTheory Filter Topology NumberField NumberField.AdelicFourier NumberField.TateGlobal

p2m_open

open scoped SchwartzMap ENNReal

noncomputable section

namespace AutomorphicForm

namespace GodementK0b

p2m_open

section Adelic

open scoped Classical

variable {F : Type} [Field F] [NumberField F]

theorem norm_apply_archRow_le (G : 𝓢((Fin 2 → mixedEmbedding.mixedSpace F), ℂ)) (N : ℕ) {S : ℝ}
    (hS0 : 0 ≤ S) (hS : ∀ y, ‖G y‖ * (1 + ‖y‖) ^ N ≤ S) {L : ℝ} (hL : 1 ≤ L)
    (g : AdelicGL2 (𝓞 F) F) (hg : colSize g ≤ L) (a : mixedEmbedding.mixedSpace F) :
    ‖G (archRow g a)‖ ≤ L ^ N * S * ((1 + ‖a‖) ^ N)⁻¹ := by
  set y := archRow g a with hy
  have h1 : ‖a‖ ≤ L * ‖y‖ :=
    (norm_le_colSize_mul_norm_archRow g a).trans (mul_le_mul_of_nonneg_right hg (norm_nonneg _))
  have h2 : 1 + ‖a‖ ≤ L * (1 + ‖y‖) := by
    calc 1 + ‖a‖ ≤ L + L * ‖y‖ := add_le_add hL h1
      _ = L * (1 + ‖y‖) := by ring
  have h3 : (1 + ‖a‖) ^ N ≤ L ^ N * (1 + ‖y‖) ^ N := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) h2 N
  have hpos : 0 < (1 + ‖a‖) ^ N := by positivity
  rw [le_mul_inv_iff₀ hpos]
  calc ‖G y‖ * (1 + ‖a‖) ^ N ≤ ‖G y‖ * (L ^ N * (1 + ‖y‖) ^ N) :=
        mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
    _ = L ^ N * (‖G y‖ * (1 + ‖y‖) ^ N) := by ring
    _ ≤ L ^ N * S := mul_le_mul_of_nonneg_left (hS y) (by positivity)

end Adelic
end GodementK0b
end AutomorphicForm
end
end P2MW.S_AutomorphicForm_integrable_and_differentiableAt_and_continuous_godementSection_of_mem_schwartzBruhat2
