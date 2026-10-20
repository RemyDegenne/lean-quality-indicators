namespace P2MW.S_NumberField_TateGlobal_exists_setIntegral_comp_ideleNorm_eq_mul_integral_Ioi_and_setIntegral_ideleNorm_cpow_eq_div

attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions

set_option autoImplicit false

p2m_open

noncomputable section

namespace NumberField

namespace TateGlobal

namespace PoleTerms

p2m_open

variable {F : Type} [Field F] [NumberField F]
  [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]

theorem setIntegral_inv_mul_gUp {w : ℂ} (hw : 0 < w.re) :
    ∫ r in Ioi (0 : ℝ), (r : ℂ)⁻¹ * gUp w r = 1 / w := by
  have hw0 : w ≠ 0 := fun h => by rw [h, zero_re] at hw; exact lt_irrefl _ hw
  have hw1 : (-w - 1).re < -1 := by rw [sub_re, neg_re, one_re]; linarith
  rw [inv_mul_gUp, setIntegral_indicator measurableSet_Ici, Ioi_inter_Ici_eq,
    setIntegral_congr_fun measurableSet_Ici (fun r hr => inv_mul_cpow_of_pos (lt_of_lt_of_le one_pos (Set.mem_Ici.mp hr)) (-w)),
    integral_Ici_eq_integral_Ioi, integral_Ioi_cpow_of_lt hw1 one_pos, sub_add_cancel, ofReal_one, one_cpow]
  field_simp

end PoleTerms
end TateGlobal
end NumberField
end
end P2MW.S_NumberField_TateGlobal_exists_setIntegral_comp_ideleNorm_eq_mul_integral_Ioi_and_setIntegral_ideleNorm_cpow_eq_div
