public section

namespace CFSG.RankThree.PartTwo.Sec16.Proof167Empty

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.KFacts

open scoped commutatorElement

theorem eq_of_isoLThreePi_two {X : Type} [Group X] [Finite X] {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hXa : Sec4.IsoLThreePi X 2 a) (hXb : Sec4.IsoLThreePi X 2 b) : a = b := by
  obtain ⟨ra, hra, heqa⟩ := three_mul_card_eq_two_pow_mul_odd ha hXa
  obtain ⟨rb, hrb, heqb⟩ := three_mul_card_eq_two_pow_mul_odd hb hXb
  have heq : 2 ^ (3 * a) * ra = 2 ^ (3 * b) * rb := by
    rw [← heqa, ← heqb]
  have h3 : 3 * a = 3 * b := Sec14.Item148Rank.eq_of_two_pow_mul_odd148 hra hrb heq
  omega

end CFSG.RankThree.PartTwo.Sec16.Proof167Empty
end
