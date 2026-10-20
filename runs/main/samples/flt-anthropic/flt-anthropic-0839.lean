namespace P2MW.S_CerednikDrinfeld_LevelU_not_le_of_mem_levelHeckeUSet

attribute [-instance] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions

set_option autoImplicit false

open scoped Quaternion TensorProduct NumberField Pointwise

open QuaternionAlgebra CerednikDrinfeld IsDedekindDomain

set_option autoImplicit false

open IsDedekindDomain NumberField

set_option autoImplicit false

open scoped TensorProduct Quaternion Pointwise

open IsDedekindDomain NumberField

noncomputable section

namespace LevelU4

scoped macro "fsr" : tactic => `(tactic| first | (ring; done) | (field_simp; done) | (field_simp; ring; done) | (simp; done) | (simp; ring; done))

section MatFwd

variable {v : HeightOneSpectrum (𝓞 ℚ)}

local notation "K" => v.adicCompletion ℚ

local notation "O" => v.adicCompletionIntegers ℚ

local notation "M2" => Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)

theorem IsInt.add {A B : M2} (hA : IsInt v A) (hB : IsInt v B) : IsInt v (A + B) := by
  intro i j
  rw [Matrix.add_apply]
  exact add_mem (hA i j) (hB i j)

end MatFwd
end LevelU4
end
end P2MW.S_CerednikDrinfeld_LevelU_not_le_of_mem_levelHeckeUSet
