@[expose] public section

lemma fourier_markov_bad_set
    (n : ℕ) (hn : 2 ≤ n)
    (q : ℤ) (hq_coprime : Int.gcd q (largestPrimeFactor n : ℤ) = 1)
    (hq_pos : 1 ≤ q) (hq_bound : (q : ℝ) < (n : ℝ) / 2) :
    ∃ B : Finset ℕ, B.card ≤
      largestPrimeFactor n ^ n.factorization (largestPrimeFactor n) /
        ⌈Real.log (n : ℝ)⌉₊ ∧
      ∀ p : ℤ, ¬ ((largestPrimeFactor n : ℤ) ∣ p) →
        1 ≤ p →
        (p : ℝ) + (q : ℝ) < (n : ℝ) / 2 →
        (p % (largestPrimeFactor n ^ n.factorization (largestPrimeFactor n) : ℕ)).toNat ∉ B →
        |(countingFunctionS n p q : ℝ) -
          (2 * ↑p - 1) * (2 * ↑q - 1) * (Nat.totient n : ℝ) / (n : ℝ) ^ 2| ≤
        9 * ⌈Real.log (n : ℝ)⌉₊ * (Nat.totient n : ℝ) *
          (1 + Real.log (n : ℝ)) ^ 2 / (largestPrimeFactor n : ℝ) := by
  obtain ⟨B, hB_card, hB_bound⟩ := error_split_bound n hn q hq_coprime hq_pos hq_bound
  exact ⟨B, hB_card, fun p hp_coprime hp_pos hp_bound hp_not_in_B => by
    have h := hB_bound p hp_coprime hp_pos hp_bound hp_not_in_B
    rw [toNat_two_mul_sub_one p hp_pos, toNat_two_mul_sub_one q hq_pos] at h
    exact le_trans h (combine_error_P0_Palpha n hn)⟩

end
