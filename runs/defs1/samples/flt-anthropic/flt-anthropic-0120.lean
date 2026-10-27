namespace P2MW.S_Matrix_finrank_linearMap_mul_card_sq_eq_finrank_mul_finrank

set_option autoImplicit false

set_option linter.unusedSectionVars false

open Module

namespace MoritaLine

section

variable {k : Type*} [Field k] {ι : Type*} [Fintype ι] [DecidableEq ι]

variable {V : Type*} [AddCommGroup V] [Module k V] [Module (Matrix ι ι k) V] [IsScalarTower k (Matrix ι ι k) V]

variable {W : Type*} [AddCommGroup W] [Module k W] [Module (Matrix ι ι k) W] [IsScalarTower k (Matrix ι ι k) W]

variable (k V) in

def ofPi (i₀ : ι) : (ι → corner k V i₀) →ₗ[k] V where
  toFun m := ∑ i, E k i i₀ • (m i : V)
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' c m := by simp [Finset.smul_sum, smul_comm_k]

end
end MoritaLine
end P2MW.S_Matrix_finrank_linearMap_mul_card_sq_eq_finrank_mul_finrank
