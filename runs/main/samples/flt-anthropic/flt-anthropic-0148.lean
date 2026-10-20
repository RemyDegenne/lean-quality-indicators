namespace P2MW.S_CerednikDrinfeld_CosetGraph_natCard_stabilizer_dart_eq_natCard_isUnitOf_conjByFiniteIdele_meetOrder_div_two

set_option autoImplicit false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

set_option linter.style.multiGoal false

set_option linter.unusedSimpArgs false

set_option synthInstance.maxHeartbeats 1600000

set_option maxHeartbeats 3200000

open scoped TensorProduct Quaternion Pointwise

open IsDedekindDomain NumberField

noncomputable section

namespace R1CDWidth

section Places

variable (q : ℕ) (hq : q.Prime)

local notation "𝔳" => place q hq

local notation "𝕂" => HeightOneSpectrum.adicCompletion ℚ (place q hq)

local notation "𝓞v" => HeightOneSpectrum.adicCompletionIntegers ℚ (place q hq)

theorem natCast_mem_asIdeal_iff (w : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    (n : 𝓞 ℚ) ∈ w.asIdeal ↔ Rat.HeightOneSpectrum.natGenerator w ∣ n := by
  rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff,
    ← map_natCast (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) n, Ideal.apply_mem_of_equiv_iff]

end Places
end R1CDWidth
end
end P2MW.S_CerednikDrinfeld_CosetGraph_natCard_stabilizer_dart_eq_natCard_isUnitOf_conjByFiniteIdele_meetOrder_div_two
