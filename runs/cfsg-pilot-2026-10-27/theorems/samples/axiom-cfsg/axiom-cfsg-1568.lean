public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

theorem exists_prime_pow_card_field (K : Type) [Field K] [Finite K] :
    ∃ p n : ℕ, p.Prime ∧ ringChar K = p ∧ Nat.card K = p ^ n := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  obtain ⟨p, hchar, n, hp, hcard⟩ := FiniteField.card' K
  haveI := hchar
  refine ⟨p, (n : ℕ), hp, ringChar.eq K p, ?_⟩
  rw [Nat.card_eq_fintype_card, hcard]

end CFSG.RankThree.PartTwo.Sec11
end
