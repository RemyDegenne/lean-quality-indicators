public section

namespace CFSG.Sporadic.Co1Schreier.OddGen

open scoped commutatorElement

theorem card_sylow_of_card_eq_mul {G : Type*} [Group G] [Finite G] {p q r : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≠ q) (hG : Nat.card G = p * q) (hr : r = p ∨ r = q) [Fact r.Prime]
    (P : Sylow r G) : Nat.card P = r := by
  rw [P.card_eq_multiplicity, hG, Nat.factorization_mul hp.ne_zero hq.ne_zero, Finsupp.add_apply,
    hp.factorization, hq.factorization]
  rcases hr with rfl | rfl
  · rw [Finsupp.single_eq_same, Finsupp.single_eq_of_ne hpq, add_zero, pow_one]
  · rw [Finsupp.single_eq_same, Finsupp.single_eq_of_ne hpq.symm, zero_add, pow_one]

end CFSG.Sporadic.Co1Schreier.OddGen
end
