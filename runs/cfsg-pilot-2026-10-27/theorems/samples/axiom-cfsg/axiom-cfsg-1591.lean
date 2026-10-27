namespace CFSG.FeitThompson

public section

set_option autoImplicit true

set_option maxSynthPendingDepth 3

open Pointwise

variable {G : Type*} [Group G]

theorem mem_conj_smul_iff {l x : G} {X : Subgroup G} :
    x ∈ MulAut.conj l • X ↔ l⁻¹ * x * l ∈ X := by
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp [MulAut.smul_def, mul_assoc]

end
end CFSG.FeitThompson
