public section

namespace CFSG.RankThree.PartTwo.Sec8.Item86ResProof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

open CFSG.RankThree.PartTwo.Sec8.Item83Proof

open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

variable {G : Type} [Group G] [Finite G]

theorem one_le_of_isoTrialityD4_or_isoGTwoEven {X : Type} [Group X] {m : ℕ}
    (h : IsoTrialityD4 X m ∨ IsoGTwoEven X (3 * m)) : 1 ≤ m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exfalso
    rcases h with ⟨q, -, -, hqe, -⟩ | ⟨K, _, _, hK, -⟩
    · exact absurd hqe q.exponent_pos.ne'
    · have h1 : 1 < Nat.card K := Finite.one_lt_card
      rw [hK] at h1
      norm_num at h1
  · exact hm

end CFSG.RankThree.PartTwo.Sec8.Item86ResProof
end
