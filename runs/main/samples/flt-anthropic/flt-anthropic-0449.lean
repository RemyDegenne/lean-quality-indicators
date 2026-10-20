namespace P2MW.S_ValuationSubring_exists_localGaloisToGlobal_mem_inertiaSubgroupIn_inv_mul_mem_fixingSubgroup

set_option autoImplicit false

open scoped NNReal

namespace P2MLeafD

open scoped Pointwise IntermediateField

section K

variable (p : ℕ) [hp : Fact p.Prime]

theorem S_antitone (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (F : IntermediateField ℚ (AlgebraicClosure ℚ))
    (n : ℕ) : S p σ F (n + 1) ⊆ S p σ F n := by
  intro τ hτ
  rw [mem_S_iff] at hτ ⊢
  exact fun e he => hτ e (lvl_mono p F (Nat.le_succ n) he)

end K
end P2MLeafD
end P2MW.S_ValuationSubring_exists_localGaloisToGlobal_mem_inertiaSubgroupIn_inv_mul_mem_fixingSubgroup
