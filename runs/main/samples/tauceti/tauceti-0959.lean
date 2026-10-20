public section

namespace TauCeti

open NumberField IsDedekindDomain nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

namespace MultiplicativeIdealWeight

section Operations

variable {S : Set (HeightOneSpectrum (𝓞 K))}

theorem IsNormTwistOnGood.pow {χ : MultiplicativeIdealWeight K} {u : ℝ}
    (h : χ.IsNormTwistOnGood u) (n : ℕ) : (χ ^ n).IsNormTwistOnGood (n * u) := by
  induction n with
  | zero =>
    rw [pow_zero, Nat.cast_zero, zero_mul, isNormTwistOnGood_zero_iff]
    exact isTrivialOnGood_one
  | succ n ih =>
    rw [pow_succ, Nat.cast_succ, add_one_mul]
    exact ih.mul h

end Operations
end MultiplicativeIdealWeight
end TauCeti
end
