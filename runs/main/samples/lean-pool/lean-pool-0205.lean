@[expose] public section

namespace PebblingLean

namespace Hypercube

namespace PaperParameters

theorem normalizedCost_recursiveCostBound_step_of_ceiling
    {K : ℝ} {n0 n : ℕ}
    (hn : n0 ≤ n) (hsmall : splitM K n < n)
    (hslack : 1 ≤ loss n * (((4 : ℝ) / 3) ^ splitA K n)) :
    normalizedCost (recursiveCostBound K n0) n ≤
      (1 + 2 * loss n) *
        normalizedCost (recursiveCostBound K n0) (splitM K n) := by
  unfold normalizedCost
  have hbase_pos : 0 < ((4 : ℝ) / 3) := by norm_num
  have hpow_n_pos : 0 < (((4 : ℝ) / 3) ^ n) := pow_pos hbase_pos n
  have hsplit : splitA K n + splitM K n = n := by
    unfold splitA
    exact Nat.sub_add_cancel (le_of_lt hsmall)
  have hpow_split : (((4 : ℝ) / 3) ^ n) =
      (((4 : ℝ) / 3) ^ splitA K n) *
        (((4 : ℝ) / 3) ^ splitM K n) := by
    rw [← pow_add, hsplit]
  have hmult := costMultiplier_le_one_add_two_loss (K := K) (n := n) hslack
  have hcost :
      (recursiveCostBound K n0 n : ℝ) ≤
        ((1 + 2 * loss n) * (((4 : ℝ) / 3) ^ splitA K n)) *
          (recursiveCostBound K n0 (splitM K n) : ℝ) := by
    rw [recursiveCostBound_step hn hsmall]
    have hprev_nonneg : 0 ≤ (recursiveCostBound K n0 (splitM K n) : ℝ) := by
      positivity
    have hmul := mul_le_mul_of_nonneg_left hmult hprev_nonneg
    simpa [Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc] using hmul
  have hdiv := div_le_div_of_nonneg_right hcost hpow_n_pos.le
  calc
    (recursiveCostBound K n0 n : ℝ) / (((4 : ℝ) / 3) ^ n)
        ≤ (((1 + 2 * loss n) * (((4 : ℝ) / 3) ^ splitA K n)) *
          (recursiveCostBound K n0 (splitM K n) : ℝ)) /
            (((4 : ℝ) / 3) ^ n) := hdiv
    _ = (1 + 2 * loss n) *
          ((recursiveCostBound K n0 (splitM K n) : ℝ) /
            (((4 : ℝ) / 3) ^ splitM K n)) := by
          rw [hpow_split]
          field_simp [pow_ne_zero _ hbase_pos.ne']

end PaperParameters
end Hypercube
end PebblingLean
end
