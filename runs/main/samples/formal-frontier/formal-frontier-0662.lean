@[expose] public section

universe u

namespace WittVector

variable {p : ℕ} [Fact p.Prime] {k : Type u} [CommRing k] [CharP k p]

theorem mul_p_pow_eq_zero_iff_coeff_pow_eq_zero (x : WittVector p k) (n : ℕ) :
    x * (p : WittVector p k) ^ n = 0 ↔ ∀ i : ℕ, x.coeff i ^ (p ^ n) = 0 := by
  constructor
  · intro h i
    simpa only [mul_pow_charP_coeff_succ, zero_coeff] using
      congrArg (fun y : WittVector p k => y.coeff (i + n)) h
  · intro h
    apply WittVector.ext
    intro i
    rw [zero_coeff]
    by_cases hi : i < n
    · exact mul_pow_charP_coeff_zero x hi
    · rw [← Nat.sub_add_cancel (Nat.le_of_not_gt hi), mul_pow_charP_coeff_succ,
        h (i - n)]

end WittVector
end
