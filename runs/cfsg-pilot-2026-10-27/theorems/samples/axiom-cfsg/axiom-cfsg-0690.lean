public section

namespace CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2

open Equiv

theorem involution_cycleType {w : Perm (Fin 7)} (hw2 : w ^ 2 = 1) (hw1 : w ≠ 1) :
    w.cycleType = Multiset.replicate 1 2 ∨ w.cycleType = Multiset.replicate 2 2 ∨
      w.cycleType = Multiset.replicate 3 2 := by
  have hord : orderOf w = 2 := orderOf_eq_prime hw2 hw1
  obtain ⟨n, hn⟩ := Perm.cycleType_prime_order (σ := w) (by rw [hord]; exact Nat.prime_two)
  rw [hord] at hn
  have hsum : (n + 1) * 2 ≤ 7 := by
    have h1 := Perm.sum_cycleType w
    rw [hn, Multiset.sum_replicate, smul_eq_mul] at h1
    rw [h1]
    exact (Finset.card_le_univ _).trans (by simp)
  have : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  rcases this with rfl | rfl | rfl
  · exact Or.inl hn
  · exact Or.inr (Or.inl hn)
  · exact Or.inr (Or.inr hn)

end CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2
end
