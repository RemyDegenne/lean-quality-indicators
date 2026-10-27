public section

namespace CFSG.RankThree.PartOne.K159F

open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.StrongP CFSG.RankThree.PartOne.K159

open Matrix MatrixGroups

open CFSG.RankThree.PartOne.Census3 (IsoLie)

theorem autWitnessN_of_isoLie_A1_three {p : ℕ} (hp5 : 5 ≤ p) {S : Type} [Group S]
    (q : TauCeti.PrimePower) (hqp : q.p = p) (hq : q.exponent = 3) (h : IsoLie S (.A 1 q)) :
    AutWitnessN p 3 6 S := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨e⟩ := nonempty_psl_two_of_isoLie q h
  subst hqp
  have hcard : Nat.card (GaloisField q.p q.exponent) = q.p ^ 3 := by
    rw [GaloisField.card q.p q.exponent (by omega), hq]
  refine AutWitnessN.of_mulEquiv e.symm
    (autWitnessN_psl_two (K := GaloisField q.p q.exponent) (p := q.p) (m := 3) (B := 6)
      (by rw [hcard]) ?_)
  rw [hcard]
  have : 5 ^ 3 ≤ q.p ^ 3 := Nat.pow_le_pow_left hp5 3
  omega

end CFSG.RankThree.PartOne.K159F
end
