public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIV

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.LocalCores

open Item434Kit Item434Alt

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem exists_e27_of_e81 {X : Type*} [Group X] {D : Subgroup X}
    (hD : CFSG.Assembly.IsElemAbelian 3 D) (hD81 : Nat.card D = 81) :
    ∃ D' : Subgroup X, CFSG.Assembly.IsElemAbelian 3 D' ∧ Nat.card D' = 27 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite D := Nat.finite_of_card_ne_zero (by rw [hD81]; norm_num)
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 3 (G := D) (n := 3)
    (by rw [hD81]; norm_num)
  refine ⟨K.map D.subtype, Source.isElemAbelian_of_le hD (Subgroup.map_subtype_le K), ?_⟩
  rw [Subgroup.card_map_of_injective D.subtype_injective, hK]
  norm_num

end CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIV
end
