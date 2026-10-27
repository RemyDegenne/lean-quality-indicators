public section

namespace CFSG.Quasithin.H13.CTK

theorem not_three_dvd_suzuki_order (a : ℕ) :
    ¬ 3 ∣ (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) * ((2 ^ (2 * a + 1)) ^ 2 + 1) := by
  have hq : 2 ^ (2 * a + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  generalize 2 ^ (2 * a + 1) = q at hq ⊢
  have h3 : Nat.Prime 3 := Nat.prime_three
  intro h
  rcases (Nat.Prime.dvd_mul h3).1 h with h | h
  · rcases (Nat.Prime.dvd_mul h3).1 h with h | h
    · have := h3.dvd_of_dvd_pow h
      omega
    · omega
  · have : (q ^ 2 + 1) % 3 = 2 := by
      rw [Nat.add_mod, pow_two, Nat.mul_mod, hq]
    omega

end CFSG.Quasithin.H13.CTK
end
