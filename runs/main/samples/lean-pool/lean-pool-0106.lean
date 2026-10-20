@[expose] public section

open MeasureTheory Homogenization

noncomputable section

namespace AVenhance.Infra.FullTheorem

open AVenhance

theorem inv_rpow_le {c R r e E : ℝ} (hc : 0 < c) (hR : 0 < R) (he : 0 ≤ e)
    (hE : c * min 1 R ^ r ≤ E) : E ^ (-e) ≤ c ^ (-e) * (1 + R ^ (-(r * e))) := by
  have hm : 0 < min 1 R := lt_min one_pos hR
  have hmr : 0 < min 1 R ^ r := Real.rpow_pos_of_pos hm r
  have hpos : 0 < c * min 1 R ^ r := mul_pos hc hmr
  have h1 : E ^ (-e) ≤ (c * min 1 R ^ r) ^ (-e) :=
    Real.rpow_le_rpow_of_nonpos hpos hE (by linarith)
  rw [Real.mul_rpow hc.le hmr.le, ← Real.rpow_mul hm.le] at h1
  have h2 : min 1 R ^ (r * -e) ≤ 1 + R ^ (-(r * e)) := by
    rcases le_total 1 R with h | h
    · rw [min_eq_left h, Real.one_rpow]
      have := Real.rpow_nonneg hR.le (-(r * e))
      linarith
    · rw [min_eq_right h, show r * -e = -(r * e) by ring]
      linarith
  have hc' : 0 ≤ c ^ (-e) := Real.rpow_nonneg hc.le _
  calc E ^ (-e) ≤ c ^ (-e) * min 1 R ^ (r * -e) := h1
    _ ≤ c ^ (-e) * (1 + R ^ (-(r * e))) := mul_le_mul_of_nonneg_left h2 hc'

end AVenhance.Infra.FullTheorem
end
end
