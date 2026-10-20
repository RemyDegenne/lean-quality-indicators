namespace P2MW.S_M4aHerbrand_exists_isAdjuster_pow_idelicArtinMap_eq_of_mem_upperRamificationGroup

attribute [-instance] ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 1600000

set_option maxSynthPendingDepth 3

open NumberField IsDedekindDomain M4aHerbrand M4aHerbrand.GenuineDescent HeckeCharacter LanglandsTunnell.P2.Artin

open scoped IsMulCommutative NumberField.PlaceDecomp

open scoped Classical Pointwise

namespace XCsup

variable (E : Type) [Field E] [NumberField E]

variable {E}

lemma finPart_locIdele_of_ne (v : HeightOneSpectrum (𝓞 E)) (a : (v.adicCompletion E)ˣ) {w : HeightOneSpectrum (𝓞 E)}
    (h : w ≠ v) : finPart w (locIdele E v a) = 1 :=
  Units.ext (locIdele_snd_of_ne v a h)

end XCsup
end P2MW.S_M4aHerbrand_exists_isAdjuster_pow_idelicArtinMap_eq_of_mem_upperRamificationGroup
