public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers

section Perfect

variable {Y : Type*} [Group Y] [Finite Y]

theorem coprime_card_of_coprime_card_quotient_pCore_two {J : Subgroup Y} {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) (h : q.Coprime (Nat.card (↥J ⧸ CFSG.pCore 2 ↥J))) :
    q.Coprime (Nat.card J) := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥J)]
  refine Nat.Coprime.mul_right h ?_
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥J))
  rw [hk]
  exact Nat.Coprime.pow_right k ((Nat.coprime_primes hq Nat.prime_two).mpr hq2)

end Perfect
end CFSG.AGLEmbedding
end
