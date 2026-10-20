public section

open MeasureTheory Set Filter Topology

open scoped ENNReal NNReal

open CKN

noncomputable section

namespace CIV

theorem abs_min_sub_min_le (a b c : ℝ) : |min a c - min b c| ≤ |a - b| := by
  have h := lipschitzWith_min.dist_le_mul (a, c) (b, c)
  simp only [Prod.dist_eq, Real.dist_eq, dist_self, NNReal.coe_one, one_mul,
    max_eq_left (abs_nonneg (a - b))] at h
  exact h

end CIV
end
end
