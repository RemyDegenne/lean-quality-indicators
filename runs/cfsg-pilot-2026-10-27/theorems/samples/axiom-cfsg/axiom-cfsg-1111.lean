public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicRank

open CFSG.AGLEmbedding CFSG.Open CFSG.SectionRank

theorem factorization_eq_of_pow_dvd {p N s : ℕ} (hp : p.Prime) (hN0 : N ≠ 0)
    (hv : p ^ s ∣ N ∧ ¬ p ^ (s + 1) ∣ N) : N.factorization p = s := by
  have h1 := (hp.pow_dvd_iff_le_factorization hN0).1 hv.1
  have h2 : ¬ s + 1 ≤ N.factorization p :=
    fun h => hv.2 ((hp.pow_dvd_iff_le_factorization hN0).2 h)
  omega

end CFSG.HardMathSupport.Timmesfeld.SporadicRank
end
