namespace P2MW.S_AutomorphicForm_exists_sum_character_mul_smooth_mul_kFinite_norm_sub_le_of_continuous_invariant_bandSupported

attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions

set_option autoImplicit false

open NumberField AutomorphicForm

open scoped Topology

noncomputable section

namespace Ws31

namespace SW3

variable (F : Type) [Field F] [NumberField F]

scoped instance : CompactSpace (T F) := NumberField.TateGlobal.compactSpace_normOneIdeleClass F

scoped instance : CompactSpace (KK F) := isCompact_iff_compactSpace.mp (AutomorphicForm.isCompact_adelicMaximalCompact F)

variable {F}

def IsKfSm (m : KK F → ℂ) : Prop :=
  ∃ V ∈ 𝓝 (1 : AdelicGL2 (𝓞 F) F), ∀ (k u : KK F),
    (u : AdelicGL2 (𝓞 F) F) ∈ V → (u : AdelicGL2 (𝓞 F) F) ∈ finiteAdelicGL2Subgroup F → m (k * u) = m k

end SW3
end Ws31
end
end P2MW.S_AutomorphicForm_exists_sum_character_mul_smooth_mul_kFinite_norm_sub_le_of_continuous_invariant_bandSupported
