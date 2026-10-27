public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup CFSG.ABGLocalTools CFSG.Assembly.LowTwoRank

open CFSG.Open (IsElemAbelian standardComponentIsStandard standardComponentOddCore ordTwistedA)

open CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.RankTwoExceptional

open CFSG.ComponentClassification.AschbacherTightEmbedding

section Orders

theorem three_dvd_card_of_psu_three {Q : Type} [Group Q] {m : ℕ}
    (h : StatedClassicalModel Q .PSU 3 2 m) : 3 ∣ Nat.card Q := by
  rw [EvenSmallLie.CatalogOrders.card_eq_lieOrd_of_classical h]
  simp only [EvenSmallLie.CatalogOrders.lieOrd, ordTwistedA]
  rw [show (3 - 1 : ℕ) = 2 from rfl, show (2 + 1 : ℕ) = 3 from rfl,
    show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair (by norm_num)]
  have ha : (((2 ^ m : ℕ) : ℤ) ^ 2 - (-1 : ℤ) ^ 2).toNat = (2 ^ m) ^ 2 - 1 := by
    have h1 : 1 ≤ (2 ^ m) ^ 2 := Nat.one_le_pow _ _ (Nat.two_pow_pos m)
    rw [show ((2 ^ m : ℕ) : ℤ) ^ 2 - (-1 : ℤ) ^ 2 = (((2 ^ m) ^ 2 - 1 : ℕ) : ℤ) by
      rw [Nat.cast_sub h1]; push_cast; ring]
    exact Int.toNat_natCast _
  have hb : (((2 ^ m : ℕ) : ℤ) ^ 3 - (-1 : ℤ) ^ 3).toNat = (2 ^ m) ^ 3 + 1 := by
    rw [show ((2 ^ m : ℕ) : ℤ) ^ 3 - (-1 : ℤ) ^ 3 = (((2 ^ m) ^ 3 + 1 : ℕ) : ℤ) by
      push_cast; ring]
    exact Int.toNat_natCast _
  rw [ha, hb]
  have h3a : 3 ∣ (2 ^ m) ^ 2 - 1 := by
    have h := Nat.sub_dvd_pow_sub_pow 4 1 m
    rw [one_pow, show (4 : ℕ) ^ m = (2 ^ m) ^ 2 by rw [← pow_mul, mul_comm, pow_mul]; norm_num]
      at h
    exact h
  have hd : Nat.gcd 3 (2 ^ m + 1) ∣ 3 := Nat.gcd_dvd_left _ _
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h3
  · rw [h1, Nat.div_one]
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_right h3a _) _
  · rw [h3]
    have hq3 : 3 ∣ 2 ^ m + 1 := h3 ▸ Nat.gcd_dvd_right 3 (2 ^ m + 1)
    have h3b : 3 ∣ (2 ^ m) ^ 3 + 1 := by
      have := Odd.nat_add_dvd_pow_add_pow (2 ^ m) 1 (by decide : Odd 3)
      rw [one_pow] at this
      exact hq3.trans this
    apply Nat.dvd_div_of_mul_dvd
    exact Dvd.dvd.mul_left (Nat.mul_dvd_mul h3a h3b) _

end Orders
end CFSG.ComponentClassification.RankTwoClassical
end
