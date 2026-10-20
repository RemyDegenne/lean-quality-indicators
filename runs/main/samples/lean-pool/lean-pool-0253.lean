@[expose] public section

noncomputable section

open Filter Set MeasureTheory

open scoped Topology ContDiff

namespace NavierStokes.RadialHeatProfile

theorem moment_slope_gap_pos {a z : ℝ} (ha : 1 < a) (hz : 0 ≤ z) :
    0 < moment a 0 z - z * moment a 1 z := by
  let f := fun v => kernel a 0 z v - z * kernel a 1 z v
  have hi : IntegrableOn f (Ioi 0) :=
    (kernel_integrable ha 0 hz).sub ((kernel_integrable ha 1 hz).const_mul z)
  have hs : Function.support f ∩ Ioi 0 = Ioi 0 := by
    rw [inter_eq_right]
    intro v hv
    exact (kernel_slope_gap_pos a hz hv).ne'
  have hp : 0 < ∫ v in Ioi 0, f v := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae]
    · rw [hs, Real.volume_Ioi, ← ENNReal.ofReal_zero]
      exact ENNReal.ofReal_lt_top
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      exact (kernel_slope_gap_pos a hz hv).le
    · exact hi
  have he := integral_sub (kernel_integrable ha 0 hz)
    ((kernel_integrable ha 1 hz).const_mul z)
  simp only [integral_const_mul] at he
  simpa only [f, he, moment] using hp

end NavierStokes.RadialHeatProfile
end
end
