@[expose] public section

open Function MeasureTheory Set

open scoped ENNReal

namespace QuadraticCarleson

theorem krauseLacey_scale_eq_eight_mul_radius (j : ℤ) :
    (2 : ℝ) ^ (j + 2) = 8 * (2 : ℝ) ^ (j - 1) := by
  rw [show j + 2 = (j - 1) + 3 by ring,
    zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  norm_num
  ring

end QuadraticCarleson
end
