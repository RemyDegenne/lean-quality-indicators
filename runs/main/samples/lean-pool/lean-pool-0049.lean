public section

open MeasureTheory Set CKN CKN.Foundation.Parabolic

open scoped Topology

noncomputable section

namespace ESS

theorem buGaussian_change_back_factor {t : ℝ} (ht : 0 < t) :
    Real.rpow t (-(5 / 2 : ℝ)) * (Real.sqrt (3 * t)) ^ 5 =
      Real.rpow 3 (5 / 2 : ℝ) := by
  have h3t : 0 < 3 * t := by positivity
  have hsquare : Real.sqrt (3 * t) ^ 5 = Real.rpow (3 * t) (5 / 2 : ℝ) := by
    have h : Real.rpow (3 * t) (5 / 2 : ℝ) =
        Real.rpow (Real.sqrt (3 * t)) (5 : ℝ) :=
      Real.rpow_div_two_eq_sqrt (x := 3 * t) (r := (5 : ℝ)) h3t.le
    exact (Real.rpow_natCast (Real.sqrt (3 * t)) 5).symm.trans h.symm
  have hmul : Real.rpow (3 * t) (5 / 2 : ℝ) =
      Real.rpow 3 (5 / 2 : ℝ) * Real.rpow t (5 / 2 : ℝ) :=
    Real.mul_rpow (x := 3) (y := t) (z := (5 / 2 : ℝ))
      (by norm_num) ht.le
  rw [hsquare, hmul]
  have hcancel : Real.rpow t (-(5 / 2 : ℝ)) * Real.rpow t (5 / 2 : ℝ) = 1 := by
    have hneg : Real.rpow t (-(5 / 2 : ℝ)) =
        (Real.rpow t (5 / 2 : ℝ))⁻¹ := Real.rpow_neg ht.le _
    rw [hneg]
    exact inv_mul_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos ht (5 / 2 : ℝ)))
  calc
    Real.rpow t (-(5 / 2 : ℝ)) *
        (Real.rpow 3 (5 / 2 : ℝ) * Real.rpow t (5 / 2 : ℝ)) =
        Real.rpow 3 (5 / 2 : ℝ) *
          (Real.rpow t (-(5 / 2 : ℝ)) * Real.rpow t (5 / 2 : ℝ)) := by ring
    _ = Real.rpow 3 (5 / 2 : ℝ) := by rw [hcancel, mul_one]

end ESS
end
end
