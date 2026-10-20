public section

namespace TauCeti

universe u v

variable {A : Type u}

section Ring

variable [Ring A]

attribute [local instance] BinomialRing.toHasUniqueDiv

theorem ringChoose_mul_pow [BinomialRing A] (m : ℕ) {a x c : A}
    (h : a * x = x * (a + c)) (hc : Commute c x) (n : ℕ) :
    Ring.choose a m * x ^ n = x ^ n * Ring.choose (a + n • c) m := by
  apply nsmul_right_injective m.factorial_ne_zero
  dsimp only
  rw [← smul_mul_assoc, ← mul_smul_comm,
    ← Ring.descPochhammer_eq_factorial_smul_choose,
    ← Ring.descPochhammer_eq_factorial_smul_choose]
  exact Polynomial.smeval_mul_pow_eq_pow_mul_smeval (descPochhammer ℤ m) h hc n

end Ring
end TauCeti
end
