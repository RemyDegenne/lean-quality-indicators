namespace P2MW.S_ModularCurve_finrank_adjoin_jqN_prime_of_not_mem

noncomputable section

p2m_open

namespace ModularCurve

namespace W1

p2m_open

variable {K : Type*} [Field K] [Algebra ℚ K]

theorem qTwist_TS_one_cycle (ζ : Kˣ) {p : ℕ} (hζp : ζ ^ p = 1) (b : ℕ) :
    qTwist ζ (TS K 1 (ζ ^ b)) = TS K 1 (ζ ^ ((b + 1) % p)) := by
  rw [qTwist_TS]
  congr 1
  have : ζ ^ ((1 : ℕ) : ℤ) * ζ ^ b = ζ ^ (b + 1) := by rw [zpow_natCast, pow_one, pow_succ']
  rw [this]
  conv_lhs => rw [← Nat.mod_add_div (b + 1) p, pow_add, pow_mul, hζp, one_pow, mul_one]

end W1
end ModularCurve
end
end P2MW.S_ModularCurve_finrank_adjoin_jqN_prime_of_not_mem
