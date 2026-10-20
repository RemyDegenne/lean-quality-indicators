namespace P2MW.S_CerednikDrinfeld_CosetGraph_exists_mem_awayUnits_mul_ne_mul_of_isDefiniteRamifiedExactlyAt

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

namespace NoncommPair

section Coord

variable {a b : ℚ}

def hatQ (w : HeightOneSpectrum (𝓞 ℚ)) (x : ℍ[ℚ, a, b]) : ℍ[w.adicCompletion ℚ, cst w a, cst w b] :=
  ⟨cst w x.re, cst w x.imI, cst w x.imJ, cst w x.imK⟩

end Coord
end NoncommPair
end
end P2MW.S_CerednikDrinfeld_CosetGraph_exists_mem_awayUnits_mul_ne_mul_of_isDefiniteRamifiedExactlyAt
