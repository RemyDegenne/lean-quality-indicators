namespace P2MW.S_QuaternionAlgebra_IsMaximalOrder_mem_ofFiniteIdele_iff_and_ofFiniteIdele_mul_mul_eq_of_mem_primeHeckeSet_of_finiteAdeleEvalAt_eq_one

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

namespace RamMaxIdele

section Q

open QuaternionAlgebra

variable {K L : Type*} [CommRing K] [CommRing L]

theorem nrd_mul' {α β : K} (x y : ℍ[K, α, β]) : nrd (x * y) = nrd x * nrd y := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x; obtain ⟨y₀, y₁, y₂, y₃⟩ := y
  simp only [QuaternionAlgebra.mk_mul_mk, nrd_mk]; ring

end Q
end RamMaxIdele
end
end P2MW.S_QuaternionAlgebra_IsMaximalOrder_mem_ofFiniteIdele_iff_and_ofFiniteIdele_mul_mul_eq_of_mem_primeHeckeSet_of_finiteAdeleEvalAt_eq_one
