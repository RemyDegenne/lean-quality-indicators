public section

namespace MvPolynomial

variable {σ R : Type*} [CommSemiring R] (p : ℕ) [ExpChar R p]

theorem _root_.FiniteField.MvPolynomial.expand_card {K : Type*} [Field K] [Fintype K]
    (f : MvPolynomial σ K) : expand (Fintype.card K) f = f ^ Fintype.card K := by
  obtain ⟨p, hp⟩ := CharP.exists K
  rcases FiniteField.card K p with ⟨⟨n, npos⟩, ⟨hp, hn⟩⟩
  have : Fact p.Prime := ⟨hp⟩
  dsimp at hn
  rw [hn, ← map_iterateFrobenius_expand p, iterateFrobenius_eq_pow,
    FiniteField.frobenius_pow hn, RingHom.one_def, map_id]

end MvPolynomial
end
