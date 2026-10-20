namespace P2MW.S_Matrix_exists_eq_mul_diagonal_mul_of_forall_mem_adicCompletionIntegers

set_option autoImplicit false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

set_option linter.style.multiGoal false

set_option linter.unusedSimpArgs false

set_option synthInstance.maxHeartbeats 1600000

open IsDedekindDomain NumberField Matrix

noncomputable section

namespace HeckeCartan

section Places

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "𝕂" => HeightOneSpectrum.adicCompletion ℚ v

local notation "𝓞v" => HeightOneSpectrum.adicCompletionIntegers ℚ v

scoped instance factPr : Fact (pr v).Prime := ⟨pr_prime v⟩

theorem mem_integers_of_valued_le_one {x : 𝕂} (hx : Valued.v x ≤ 1) : x ∈ 𝓞v :=
  (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).2 hx

end Places
end HeckeCartan
end
end P2MW.S_Matrix_exists_eq_mul_diagonal_mul_of_forall_mem_adicCompletionIntegers
