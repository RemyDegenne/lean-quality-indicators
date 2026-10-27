public noncomputable section

namespace CFSG.ComponentClassification.AutL2Facts

open CFSG Finset

universe u

theorem two_pow_add_dvd_pow_two_pow_sub_one {t : ℤ} (ht : Odd t) {k : ℕ}
    (h : (2 : ℤ) ^ k ∣ t - 1 ∨ (2 : ℤ) ^ k ∣ t + 1) :
    ∀ e : ℕ, 1 ≤ e → (2 : ℤ) ^ (k + e) ∣ t ^ (2 ^ e) - 1 := by
  intro e he
  induction e with
  | zero => omega
  | succ e ih =>
    rcases Nat.eq_zero_or_pos e with rfl | hpos
    · have h2m : (2 : ℤ) ∣ t - 1 := by
        rcases ht with ⟨m, rfl⟩; exact ⟨m, by ring⟩
      have h2p : (2 : ℤ) ∣ t + 1 := by
        rcases ht with ⟨m, rfl⟩; exact ⟨m + 1, by ring⟩
      have hsq : t ^ (2 ^ (0 + 1)) - 1 = (t - 1) * (t + 1) := by ring
      rw [hsq, pow_succ]
      rcases h with h | h
      · exact mul_dvd_mul h h2p
      · rw [mul_comm (t - 1)]
        exact mul_dvd_mul h h2m
    · have ih' := ih hpos
      have hodd : Odd (t ^ 2 ^ e) := ht.pow
      have h2 : (2 : ℤ) ∣ t ^ 2 ^ e + 1 := by
        rcases hodd with ⟨m, hm⟩; exact ⟨m + 1, by rw [hm]; ring⟩
      have hfac : t ^ (2 ^ (e + 1)) - 1 = (t ^ 2 ^ e - 1) * (t ^ 2 ^ e + 1) := by ring
      rw [hfac, ← add_assoc, pow_succ]
      exact mul_dvd_mul ih' h2

end CFSG.ComponentClassification.AutL2Facts
end
