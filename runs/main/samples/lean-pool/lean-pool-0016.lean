@[expose] public section

open Real Complex Function TopologicalSpace Filter Topology Metric MeasureTheory Nat

variable {f g : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} {z z₀ c : ℂ} {n : ℕ} {U : Set ℂ} {r : ℝ}

lemma exists_cindex_eq_order (hp : HasFPowerSeriesAt f p z₀) :
    ∃ R > (0 : ℝ), ∀ r ∈ Set.Ioo 0 R, cindex z₀ r f = p.order := by
  by_cases h : p = 0
  case neg => exact exists_cindex_eq_order' hp h
  case pos =>
    subst_vars
    obtain ⟨R, hR, hf⟩ := Metric.eventually_nhds_iff.mp (hp.locally_zero_iff.mpr rfl)
    refine ⟨R, hR, fun r hr => ?_⟩
    have heq : Set.EqOn (fun z => deriv f z / f z) 0 (sphere z₀ r) := by
      intro z hz
      have hd : dist z z₀ < R := by
        rw [mem_sphere_iff_norm, ← Complex.dist_eq] at hz
        simpa [hz] using hr.2
      simp_all
    simp only [cindex, mul_inv_rev, inv_I, neg_mul, FormalMultilinearSeries.order_zero,
      CharP.cast_eq_zero, neg_eq_zero, _root_.mul_eq_zero, I_ne_zero, inv_eq_zero,
      ofReal_eq_zero, pi_ne_zero, OfNat.ofNat_ne_zero, or_self, false_or]
    rw [circleIntegral.integral_congr hr.1.le heq]
    simp [circleIntegral]

end
