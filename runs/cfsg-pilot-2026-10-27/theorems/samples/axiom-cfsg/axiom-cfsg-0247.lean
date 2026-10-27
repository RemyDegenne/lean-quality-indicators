public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.LocalRank

namespace Proof1513Res3

section All

variable {G : Type} [Group G] [Finite G]

open CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS

open scoped commutatorElement

theorem le_of_le_sup_zpowers {S M : Subgroup G} {b : G} (hS2 : IsPGroup 2 S)
    (hSM : S ≤ Subgroup.normalizer (M : Set G)) (hbM : b ∈ Subgroup.normalizer (M : Set G))
    (hb3 : b ^ 3 = 1) (hSb : S ≤ M ⊔ Subgroup.zpowers b) : S ≤ M := by
  refine le_of_le_sup_of_odd hS2 ?_ hSM (Subgroup.zpowers_le.mpr hbM) hSb
  rw [Nat.card_zpowers]
  intro h2
  have h3 : orderOf b ∣ 3 := orderOf_dvd_of_pow_eq_one hb3
  have := Nat.le_of_dvd (by norm_num) (h2.trans h3)
  have h1 : orderOf b ≠ 1 := by
    intro h1
    rw [h1] at h2
    norm_num at h2
  rcases (Nat.dvd_prime Nat.prime_three).mp h3 with h | h
  · exact h1 h
  · rw [h] at h2
    norm_num at h2

end All
end Proof1513Res3
end CFSG.RankThree.PartTwo.Sec15
end
