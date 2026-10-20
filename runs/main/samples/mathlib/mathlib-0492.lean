public section

open Real Set Filter MeasureTheory intervalIntegral

open scoped Topology

theorem integral_Ioi_cpow_of_lt {a : ℂ} (ha : a.re < -1) {c : ℝ} (hc : 0 < c) :
    (∫ t : ℝ in Ioi c, (t : ℂ) ^ a) = -(c : ℂ) ^ (a + 1) / (a + 1) := by
  refine
    tendsto_nhds_unique
      (intervalIntegral_tendsto_integral_Ioi c (integrableOn_Ioi_cpow_of_lt ha hc) tendsto_id) ?_
  suffices
    Tendsto (fun x : ℝ => ((x : ℂ) ^ (a + 1) - (c : ℂ) ^ (a + 1)) / (a + 1)) atTop
      (𝓝 <| -c ^ (a + 1) / (a + 1)) by
    refine this.congr' ((eventually_gt_atTop 0).mp (Eventually.of_forall fun x hx => ?_))
    dsimp only
    rw [integral_cpow, id]
    refine Or.inr ⟨?_, notMem_uIcc_of_lt hc hx⟩
    apply_fun Complex.re
    rw [Complex.neg_re, Complex.one_re]
    exact ha.ne
  simp_rw [← zero_sub, sub_div]
  refine (Tendsto.div_const ?_ _).sub_const _
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine
    (tendsto_rpow_neg_atTop (by linarith : 0 < -(a.re + 1))).congr'
      ((eventually_gt_atTop 0).mp (Eventually.of_forall fun x hx => ?_))
  simp_rw [neg_neg, Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.add_re, Complex.one_re]

end
