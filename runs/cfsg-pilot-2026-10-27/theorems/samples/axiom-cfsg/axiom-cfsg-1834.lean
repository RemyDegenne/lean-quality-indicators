public section

namespace CFSG.RankThree.PartTwo.Sec15.F153L3K

section Glue

open scoped MatrixGroups Matrix

open CFSG.LargeExtraspecial

theorem odd_card_center_sl (F : Type) [Field F] [Finite F] :
    Odd (Nat.card (Subgroup.center SL(3, F))) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hodd
  have h2 : 2 ∣ Nat.card (Subgroup.center SL(3, F)) := by
    rcases Nat.even_or_odd (Nat.card (Subgroup.center SL(3, F))) with he | ho
    · exact even_iff_two_dvd.1 he
    · exact absurd ho hodd
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center SL(3, F)) 2 h2
  have h3 : (g : SL(3, F)) ^ 3 = 1 := pow_three_eq_one_of_mem_center g.2
  have h4 : orderOf (g : SL(3, F)) ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  rw [Subgroup.orderOf_coe, hg] at h4
  omega

end Glue
end CFSG.RankThree.PartTwo.Sec15.F153L3K
end
