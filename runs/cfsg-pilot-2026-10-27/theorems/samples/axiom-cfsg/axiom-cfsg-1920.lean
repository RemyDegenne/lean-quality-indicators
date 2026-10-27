public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Flag

open CFSG.LocalAnalysis.ComponentInitial

variable {m : ℕ}

theorem invCount_le (σ : Equiv.Perm (Fin (m + 1))) : invCount σ ≤ (m + 1) * m / 2 := by
  rw [invCount]
  have hsub : (Finset.univ.filter fun p : Fin (m + 1) × Fin (m + 1) =>
      p.1 < p.2 ∧ σ p.2 < σ p.1) ⊆
      (Finset.univ.filter fun p : Fin (m + 1) × Fin (m + 1) => p.1 < p.2) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact hp.1
  have hcard := Finset.card_le_card hsub
  rw [Fintype.card_product_filter_lt] at hcard
  simpa [Nat.choose_two_right] using hcard

end CFSG.ClassicalInvolution.Phan.PhanE.Flag
end
