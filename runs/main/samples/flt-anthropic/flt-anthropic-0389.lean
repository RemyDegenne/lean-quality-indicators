namespace P2MW.S_CerednikDrinfeld_uHeckeSet_cosetDictionary_of_mem_primeHeckeSet

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

namespace CosetDict

section Places

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "𝕂" => HeightOneSpectrum.adicCompletion ℚ v

local notation "𝓞v" => HeightOneSpectrum.adicCompletionIntegers ℚ v

scoped instance factPr : Fact (pr v).Prime := ⟨pr_prime v⟩

theorem pr_mem_integers : ((pr v : ℕ) : 𝕂) ∈ 𝓞v := natCast_mem_integers v _

end Places
end CosetDict
end
end P2MW.S_CerednikDrinfeld_uHeckeSet_cosetDictionary_of_mem_primeHeckeSet
