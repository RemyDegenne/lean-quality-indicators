public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer

theorem rho0_mem_R0 : rho0 ∈ R0 := by
  rw [show rho0 = (a0 * b0) * (c0 * b0) by decide]
  exact mul_mem a0_b0_mem_R0 c0_b0_mem_R0

end CFSG.ComponentClassification.HSFLit
end
