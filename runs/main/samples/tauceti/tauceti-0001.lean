public section

open Matrix Matrix.SpecialLinearGroup

open scoped MatrixGroups Pointwise

variable {N : ℕ}

namespace CongruenceSubgroup

theorem Gamma0_index_mul_prod_primeFactors {N : ℕ} (hN : N ≠ 0) :
    (Gamma0 N).index * ∏ p ∈ N.primeFactors, p = N * ∏ p ∈ N.primeFactors, (p + 1) := by
  rw [Gamma0_index_eq_prod_factorization hN]
  conv_rhs => arg 1; rw [← Nat.prod_factorization_pow_eq_self hN]
  simp only [Nat.prod_primeFactors_prod_factorization, ← Finsupp.prod_mul]
  refine Finsupp.prod_congr (M := ℕ) (N := ℕ) fun p hp ↦ ?_
  rw [Finsupp.mem_support_iff, ← zero_lt_iff] at hp
  rw [mul_right_comm, ← pow_succ, Nat.sub_add_cancel hp]

end CongruenceSubgroup
end
