namespace P2MW.S_CerednikDrinfeld_LevelU_ofFiniteIdele_mul_inf_ofFiniteIdele_mul_eq_of_mem_levelHeckeUSet

attribute [-instance] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions

section Pen20Lift

open scoped Quaternion TensorProduct NumberField Pointwise

p2m_open

section LevelULocalBlock

set_option autoImplicit false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

set_option linter.style.multiGoal false

set_option linter.unusedSimpArgs false

set_option synthInstance.maxHeartbeats 1600000

set_option maxHeartbeats 3200000

open scoped TensorProduct Quaternion Pointwise

open IsDedekindDomain NumberField Matrix

noncomputable section

namespace LevelULocal

section LocalMatrix

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "𝕂" => HeightOneSpectrum.adicCompletion ℚ v

local notation "𝓞v" => HeightOneSpectrum.adicCompletionIntegers ℚ v

local notation "M₂" => Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v)

local notation "ϖ" => (((pr v : ℕ) : HeightOneSpectrum.adicCompletion ℚ v))

def tMi : M₂ := !![1, 0; 0, ϖ⁻¹]

end LocalMatrix
end LevelULocal
end
end LevelULocalBlock
end Pen20Lift
end P2MW.S_CerednikDrinfeld_LevelU_ofFiniteIdele_mul_inf_ofFiniteIdele_mul_eq_of_mem_levelHeckeUSet
