namespace OAI

noncomputable section

open Filter Topology

namespace Problem340.SparseLogBound

theorem principalRate_le_rate (m P Q τ J : ℝ) (hm : 0 < m)
    (hP : 1 ≤ P) (hQ : 1 ≤ Q) (hJ : 0 ≤ J)
    {r : ℕ} (hr : 0 < r) :
    principalRate m P Q τ ≤ rate m P Q τ J r := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hceil : τ * (r : ℝ) ≤ (⌈τ * (r : ℝ) + J⌉₊ : ℝ) := by
    exact (le_add_of_nonneg_right hJ).trans (Nat.le_ceil _)
  rw [rate, log_code_count P Q τ J (by linarith) (by linarith)]
  calc
    principalRate m P Q τ =
      ((r : ℝ) * Real.log 2 + (r : ℝ) * Real.log P +
        (τ * (r : ℝ)) * Real.log Q) / (m * (r : ℝ)) := by
      unfold principalRate
      field_simp
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (mul_pos hm hr').le
      exact add_le_add_right
        (mul_le_mul_of_nonneg_right hceil (Real.log_nonneg hQ)) _

end Problem340.SparseLogBound
end
end OAI
