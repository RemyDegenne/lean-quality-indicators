public section

namespace CFSG.GH74.GLS.Th2.L83

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Th2

open CFSG.GH74.GLS.C3.Layer1 CFSG.Blueprint CFSG.Assembly.LowTwoRank

open scoped commutatorElement

variable {G : Type} [Group G]

variable [Finite G]

theorem eq_five_of_ordA_one_eq_sixty {m : ℕ} (hodd : Odd m) (h : CFSG.Open.ordA 1 m = 60) : m = 5 := by
  unfold CFSG.Open.ordA at h
  rw [show 1 * (1 + 1) / 2 = 1 by rfl, pow_one, show Finset.Icc 2 (1 + 1) = {2} by rfl,
    Finset.prod_singleton] at h
  rcases Nat.lt_or_ge m 10 with hm | hm
  · have hodd' : m % 2 = 1 := Nat.odd_iff.1 hodd
    interval_cases m <;> simp_all
  · exfalso
    have hg : 0 < Nat.gcd 2 (m - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
    have hle : Nat.gcd 2 (m - 1) ≤ 2 := Nat.gcd_le_left _ (by norm_num)
    have hX : 2 * (60 + 1) ≤ m * (m ^ 2 - 1) := by
      have h1 : 10 * 99 ≤ m * (m ^ 2 - 1) := by
        have h2 : 99 ≤ m ^ 2 - 1 := by
          have : 10 ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left hm 2
          omega
        exact Nat.mul_le_mul hm h2
      omega
    have := Th2.lt_div_aux hg hle hX
    rw [h] at this
    exact lt_irrefl _ this

end CFSG.GH74.GLS.Th2.L83
end
