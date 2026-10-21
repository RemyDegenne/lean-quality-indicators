namespace OAI

section

namespace Erdos3

theorem linearRestrictionArithmeticBudget_le_exp (n m d H K : ℕ) {p P Q : ℝ}
    (hp : 0 ≤ p) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hn : (n : ℝ) ≤ p) (hm : (m : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp P) (hK : (K : ℝ) ≤ Real.exp Q) :
    (((((n + 1) ^ d * K) * (m * H + 1) ^ d) *
      (K ^ ((n + 1) ^ d) * H ^ ((n * m) * d)) : ℕ) : ℝ) ≤
        Real.exp ((d : ℝ) * p + Q + (d : ℝ) * (p + P + 1) +
          (p + 1) ^ d * Q + p * p * d * P) := by
  have hn1 : (n : ℝ) + 1 ≤ Real.exp p :=
    (add_le_add hn (le_refl 1)).trans (Real.add_one_le_exp p)
  have hnPow : ((n : ℝ) + 1) ^ d ≤ Real.exp ((d : ℝ) * p) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by positivity) hn1 d
  have hmexp : (m : ℝ) ≤ Real.exp p := by
    exact hm.trans ((le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp p))
  have hmH : (m : ℝ) * H ≤ Real.exp (p + P) := by
    rw [Real.exp_add]
    exact mul_le_mul hmexp hH (Nat.cast_nonneg H) (Real.exp_nonneg p)
  have hmH1 : (m : ℝ) * H + 1 ≤ Real.exp (p + P + 1) := by
    simpa only [add_comm] using one_add_le_exp_succ (add_nonneg hp hP) hmH
  have hmPow : ((m : ℝ) * H + 1) ^ d ≤ Real.exp ((d : ℝ) * (p + P + 1)) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by positivity) hmH1 d
  have hKPow : (K : ℝ) ^ ((n + 1) ^ d) ≤ Real.exp ((p + 1) ^ d * Q) := by
    calc
      _ ≤ (Real.exp Q) ^ ((n + 1) ^ d) := pow_le_pow_left₀ (Nat.cast_nonneg K) hK _
      _ = Real.exp ((((n : ℝ) + 1) ^ d) * Q) := by
        rw [← Real.exp_nat_mul]
        simp only [Nat.cast_pow, Nat.cast_add, Nat.cast_one]
      _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (by positivity) (add_le_add hn (le_refl 1)) d) hQ)
  have hHPow : (H : ℝ) ^ ((n * m) * d) ≤ Real.exp (p * p * d * P) := by
    calc
      _ ≤ (Real.exp P) ^ ((n * m) * d) := pow_le_pow_left₀ (Nat.cast_nonneg H) hH _
      _ = Real.exp ((n : ℝ) * m * d * P) := by
        rw [← Real.exp_nat_mul]
        simp only [Nat.cast_mul]
      _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul hn hm (Nat.cast_nonneg m) hp)
          (Nat.cast_nonneg d)) hP)
  have hfront := mul_le_mul hnPow hK (Nat.cast_nonneg K) (Real.exp_nonneg _)
  have hscaled := mul_le_mul hfront hmPow (by positivity) (by positivity)
  have hden := mul_le_mul hKPow hHPow (by positivity) (Real.exp_nonneg _)
  have htotal := mul_le_mul hscaled hden (by positivity) (by positivity)
  push_cast
  refine htotal.trans_eq ?_
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

end Erdos3
end
end OAI
