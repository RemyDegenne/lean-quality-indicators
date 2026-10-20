@[expose] public section

local macro_rules | `($x ^ $n:num) => `($x ^ ($n : ℕ))

noncomputable section

namespace NavierStokes.ShapedWaitBounds

open Set Filter MeasureTheory

open scoped Topology ContDiff

open OutgoingSchedule OutgoingTail NaturalAxisData OutgoingEntranceCone

theorem weighted_bound_of_angular_square (c : Parameters) (η : ℝ) {t B z : ℝ}
    (ht : 0 ≤ t) (hB : 0 ≤ B)
    (hz : |z| ≤ B * angular c.P c.dropLength c.lam (c.holdStart + t, η) ^ 2) :
    |Real.exp t * z| ≤ B * angular c.P c.dropLength c.lam (c.holdStart, η) ^ 2 := by
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  have he : Real.exp (-2 * c.lam * t) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith only [ht, mul_nonneg c.lam_pos.le ht])
  calc
    _ ≤ B * (Real.exp t * angular c.P c.dropLength c.lam (c.holdStart + t, η) ^ 2) := by
      linarith only [hz, mul_le_mul_of_nonneg_left hz (Real.exp_pos t).le]
    _ = B * (angular c.P c.dropLength c.lam (c.holdStart, η) ^ 2 * Real.exp (-2 * c.lam * t)) := by
      rw [weighted_angular_square_hold c η ht]
    _ ≤ _ := by
      have hm := mul_le_mul_of_nonneg_left he
        (mul_nonneg hB (sq_nonneg (angular c.P c.dropLength c.lam (c.holdStart, η))))
      linarith only [hm]

end NavierStokes.ShapedWaitBounds
end
end
