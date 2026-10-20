public section

open scoped BigOperators

namespace Matrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem relEntropy_nonneg_of_nonneg {P Q : Matrix ι κ ℝ} (hQ : ∀ i j, 0 ≤ Q i j)
    (hP : ∀ i j, 0 ≤ P i j) (hQP : ∀ i j, P i j = 0 → Q i j = 0)
    (hmass : ∑ i, ∑ j, Q i j = ∑ i, ∑ j, P i j) : 0 ≤ relEntropy Q P := by
  -- Each cell satisfies `Q - P ≤ Q * log Q - Q * log P`, and the left sides add up to `0`.
  have hcell : ∀ i j, Q i j - P i j ≤ Q i j * Real.log (Q i j) - Q i j * Real.log (P i j) := by
    intro i j
    rcases (hP i j).eq_or_lt with h | h
    · simp [hQP i j h.symm, ← h]
    · linarith [Real.mul_log_sub_mul_log_ge (P i j) (Q i j) h (hQ i j)]
  calc (0 : ℝ) = ∑ i, ∑ j, (Q i j - P i j) := by simp [Finset.sum_sub_distrib, hmass]
    _ ≤ relEntropy Q P := by
      rw [relEntropy_def]
      exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hcell i j

end Matrix
end
