public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance.AutL3Arith

theorem bndZ {ℓ k t a b : ℕ} (hℓ : ℓ.Prime) (ha : 0 < a)
    (hab : (a = t ∧ b = t + 2) ∨ (a = t + 3 ∧ b = t + 1))
    (h : ℓ ^ k ∣ a ^ 2 * (b * (t ^ 2 + 3 * t + 3))) : ℓ ^ k ≤ 4 * (t + 3) ^ 2 := by
  have hb : 0 < b := by omega
  have hc : 0 < t ^ 2 + 3 * t + 3 := by positivity
  have hat : a ≤ t + 3 := by omega
  have hbt : b ≤ t + 3 := by omega
  have e1 : a ^ 2 ≤ (t + 3) ^ 2 := Nat.pow_le_pow_left hat 2
  have hZ : t ^ 2 + 3 * t + 3 ≤ 4 * (t + 3) ^ 2 := by nlinarith
  have hb3 : b ≤ (t + 3) ^ 2 := le_trans hbt (Nat.le_self_pow (by norm_num) (t + 3))
  by_cases h2 : ℓ = 2
  · subst h2
    have hc2 : (t ^ 2 + 3 * t + 3) % 2 = 1 := by
      rcases Nat.even_or_odd' t with ⟨m, hm | hm⟩
      · have : t ^ 2 + 3 * t + 3 = 2 * (2 * m ^ 2 + 3 * m + 1) + 1 := by rw [hm]; ring
        omega
      · have : t ^ 2 + 3 * t + 3 = 2 * (2 * m ^ 2 + 5 * m + 3) + 1 := by rw [hm]; ring
        omega
    have h1 : 2 ^ k ∣ a ^ 2 * b :=
      (Nat.Coprime.pow_left k (coprime_of_not_dvd (n := t ^ 2 + 3 * t + 3) Nat.prime_two
        (by omega))).dvd_of_dvd_mul_right (by rwa [← mul_assoc] at h)
    have hpar : a % 2 = b % 2 := by omega
    by_cases hao : a % 2 = 1
    · have hn : Nat.Coprime (2 ^ k) (a ^ 2 * b) := by
        refine Nat.Coprime.pow_left k (coprime_of_not_dvd Nat.prime_two fun hh => ?_)
        rcases (Nat.Prime.dvd_mul Nat.prime_two).1 hh with h3 | h3
        · have := Nat.prime_two.dvd_of_dvd_pow h3
          omega
        · omega
      have := Nat.Coprime.eq_one_of_dvd hn h1
      rw [this]
      exact Nat.succ_le_of_lt (by positivity)
    · obtain ⟨m, hm⟩ : ∃ m, a = 2 * m := ⟨a / 2, by omega⟩
      obtain ⟨n, hn⟩ : ∃ n, b = 2 * n := ⟨b / 2, by omega⟩
      have hmn : m = n + 1 ∨ n = m + 1 := by omega
      have hfac : a ^ 2 * b = 8 * (m ^ 2 * n) := by rw [hm, hn]; ring
      rw [hfac] at h1
      by_cases hmo : m % 2 = 1
      · have hm2 : m ^ 2 % 2 = 1 := by rw [Nat.pow_mod]; simp [hmo]
        have h4 : 2 ^ k ∣ m ^ 2 * (8 * n) := by
          have : m ^ 2 * (8 * n) = 8 * (m ^ 2 * n) := by ring
          rw [this]; exact h1
        have h5 : 2 ^ k ∣ 8 * n :=
          (Nat.Coprime.pow_left k (coprime_of_not_dvd Nat.prime_two (by omega))).dvd_of_dvd_mul_left
            h4
        have := Nat.le_of_dvd (by omega) h5
        omega
      · have h4 : 2 ^ k ∣ (8 * m ^ 2) * n := by
          have : (8 * m ^ 2) * n = 8 * (m ^ 2 * n) := by ring
          rw [this]; exact h1
        have h5 : 2 ^ k ∣ 8 * m ^ 2 :=
          (Nat.Coprime.pow_left k (coprime_of_not_dvd Nat.prime_two (by omega))).dvd_of_dvd_mul_right
            h4
        have := Nat.le_of_dvd (by
          have : 0 < m := by omega
          positivity) h5
        have ham : a ^ 2 = 4 * m ^ 2 := by rw [hm]; ring
        omega
  by_cases h3 : ℓ = 3
  · subst h3
    have hab' : 3 ∣ a → 3 ∣ b → False := by
      intro h1 h2'
      rcases hab with ⟨ha', hb'⟩ | ⟨ha', hb'⟩ <;> omega
    have hbc : 3 ∣ b → 3 ∣ t ^ 2 + 3 * t + 3 → False := by
      intro h1 h2'
      rcases hab with ⟨ha', hb'⟩ | ⟨ha', hb'⟩
      · obtain ⟨n, hn⟩ : ∃ n, t = 3 * n + 1 := ⟨t / 3, by omega⟩
        rw [hn] at h2'
        have : (3 * n + 1) ^ 2 + 3 * (3 * n + 1) + 3 = 3 * (3 * n ^ 2 + 5 * n + 2) + 1 := by ring
        rw [this] at h2'
        omega
      · obtain ⟨n, hn⟩ : ∃ n, t = 3 * n + 2 := ⟨t / 3, by omega⟩
        rw [hn] at h2'
        have : (3 * n + 2) ^ 2 + 3 * (3 * n + 2) + 3 = 3 * (3 * n ^ 2 + 7 * n + 4) + 1 := by ring
        rw [this] at h2'
        omega
    have hac : 3 ∣ a → 3 ∣ t ^ 2 + 3 * t + 3 → ∃ c', t ^ 2 + 3 * t + 3 = 3 * c' ∧ ¬ 3 ∣ c' := by
      intro h1 _
      obtain ⟨n, hn⟩ : ∃ n, t = 3 * n := by
        rcases hab with ⟨ha', hb'⟩ | ⟨ha', hb'⟩
        · exact ⟨t / 3, by omega⟩
        · exact ⟨t / 3, by omega⟩
      refine ⟨3 * n ^ 2 + 3 * n + 1, ?_, by omega⟩
      rw [hn]; ring
    rcases abs_bound hℓ ha hb hc (by norm_num) hab' hbc hac h with h6 | h6 | h6 <;> omega
  · have hd2 : ¬ ℓ ∣ 2 := fun hh => h2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 hh)
    have hd3 : ¬ ℓ ∣ 3 := fun hh => h3 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).1 hh)
    have hd1 : ¬ ℓ ∣ 1 := fun hh => hℓ.ne_one (Nat.dvd_one.1 hh)
    have hab' : ℓ ∣ a → ℓ ∣ b → False := by
      intro h1 h2'
      rcases hab with ⟨ha', hb'⟩ | ⟨ha', hb'⟩
      · rw [ha'] at h1; rw [hb'] at h2'
        exact hd2 (dvd_diff h1 h2' rfl)
      · rw [ha'] at h1; rw [hb'] at h2'
        exact hd2 (dvd_diff h2' h1 (by omega))
    have hbc : ℓ ∣ b → ℓ ∣ t ^ 2 + 3 * t + 3 → False := by
      intro h1 h2'
      rcases hab with ⟨ha', hb'⟩ | ⟨ha', hb'⟩
      · rw [hb'] at h1; exact hd1 (dvd_Z_t2 h1 h2')
      · rw [hb'] at h1; exact hd1 (dvd_Z_t1 h1 h2')
    have hac : ℓ ∣ a → ℓ ∣ t ^ 2 + 3 * t + 3 →
        ∃ c', t ^ 2 + 3 * t + 3 = 1 * c' ∧ ¬ ℓ ∣ c' := by
      intro h1 h2'
      exfalso
      rcases hab with ⟨ha', hb'⟩ | ⟨ha', hb'⟩
      · rw [ha'] at h1; exact hd3 (dvd_Z_t h1 h2')
      · rw [ha'] at h1; exact hd3 (dvd_Z_t3 h1 h2')
    rcases abs_bound hℓ ha hb hc (by norm_num) hab' hbc hac h with h6 | h6 | h6 <;> omega

end CFSG.HardMathSupport.Solomon.LocalBalance.AutL3Arith
end
