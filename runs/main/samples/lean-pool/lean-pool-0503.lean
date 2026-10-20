@[expose] public section

noncomputable section MetricCodesNoncomputable

namespace MetricCodes

section

open Filter Metric Topology

open scoped BigOperators InnerProductSpace Topology

namespace Hamming

theorem threshold_ceil_numerator_le_two {δ : ℝ}
    (hδ : δ ≤ 1) {n : ℕ} (hn : 0 < n) :
    1 - threshold n (Nat.ceil (δ * (n : ℝ))) ≤ 2 := by
  have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hdreal : (Nat.ceil (δ * (n : ℝ)) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast ceil_distance_le_dimension hδ n
  have hquot :
      2 * (Nat.ceil (δ * (n : ℝ)) : ℝ) / (n : ℝ) ≤ 2 := by
    apply (div_le_iff₀ hnreal).2
    exact mul_le_mul_of_nonneg_left hdreal (by norm_num)
  unfold threshold
  linarith

end Hamming
end
end MetricCodes
end MetricCodesNoncomputable
end
