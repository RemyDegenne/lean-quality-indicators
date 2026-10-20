@[expose] public section

open ArithmeticFunction

open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

theorem moebius_restricted_sum (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (hmn : m ∣ n) :
    ∑ x ∈ n.divisorsAntidiagonal with m ∣ x.2, (μ x.1 : ℤ) = if n = m then 1 else 0 := by
  have hm_pos : 0 < m := by lia
  have classic : ∀ N ≥ 1, ∑ i ∈ N.divisors, (μ i : ℤ) = if N = 1 then 1 else 0 := by
    intro N hN
    simpa [ArithmeticFunction.moebius_mul_coe_zeta, ArithmeticFunction.one_apply] using
      (ArithmeticFunction.coe_mul_zeta_apply (f := μ) (x := N)).symm
  obtain ⟨N, rfl⟩ := hmn
  have hN0 : 1 ≤ N := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
  have hbij : ∑ x ∈ (m * N).divisorsAntidiagonal with m ∣ x.2, (μ x.1 : ℤ)
      = ∑ y ∈ N.divisorsAntidiagonal, (μ y.1 : ℤ) := by
    apply Finset.sum_nbij' (fun x ↦ (x.1, x.2 / m)) (fun y ↦ (y.1, y.2 * m))
    · rintro ⟨e, d⟩ hx
      simp only [Finset.mem_filter, Nat.mem_divisorsAntidiagonal] at hx ⊢
      obtain ⟨⟨hed, hne⟩, ⟨d', rfl⟩⟩ := hx
      rw [Nat.mul_div_cancel_left _ hm_pos]
      exact ⟨Nat.eq_of_mul_eq_mul_left hm_pos (by nlinarith), by rintro rfl; simp at hne⟩
    · rintro ⟨e, d'⟩ hy
      simp only [Finset.mem_filter, Nat.mem_divisorsAntidiagonal] at hy ⊢
      obtain ⟨hed, hne⟩ := hy
      exact ⟨⟨by rw [← hed]; ring, by positivity⟩, ⟨d', by ring⟩⟩
    · rintro ⟨e, d⟩ hx
      simp only [Finset.mem_filter, Nat.mem_divisorsAntidiagonal] at hx
      obtain ⟨⟨hed, hne⟩, ⟨d', rfl⟩⟩ := hx
      simp [Nat.mul_div_cancel_left _ hm_pos, mul_comm]
    · rintro ⟨e, d'⟩ hy
      simp [Nat.mul_div_cancel _ hm_pos]
    · rintro ⟨e, d⟩ hx
      rfl
  rw [hbij, Nat.sum_divisorsAntidiagonal (fun i j ↦ (μ i : ℤ)), classic N hN0]
  simp only [show (m * N = m) ↔ (N = 1) from
    ⟨fun h ↦ Nat.eq_of_mul_eq_mul_left hm_pos (h.trans (by ring)), fun h ↦ by rw [h, mul_one]⟩]

end
