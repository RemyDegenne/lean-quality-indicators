public section

noncomputable section

open Complex MeasureTheory Metric Real Set Filter Topology

open scoped NNReal ENNReal

namespace TauCeti

variable {f : ℂ → ℂ} {c w : ℂ} {R : ℝ}

theorem _root_.MeasureTheory.Measure.re_herglotzTransform_nonneg
    (μ : Measure Circle) (hw : w ∈ ball (0 : ℂ) 1) :
    0 ≤ (μ.herglotzTransform w).re := by
  rw [Measure.herglotzTransform_def]
  by_cases hint : Integrable (fun z : Circle ↦ ((z : ℂ) + w) / ((z : ℂ) - w)) μ
  swap
  · simp [integral_undef hint]
  rw [← reCLM_apply, ← reCLM.integral_comp_comm hint]
  refine integral_nonneg fun z ↦ ?_
  have hnonneg : 0 ≤ (1 - ‖w‖) / (1 + ‖w‖) :=
    div_nonneg (sub_nonneg.2 (mem_ball_zero_iff.1 hw).le) (by positivity)
  exact hnonneg.trans (by simpa using
    le_re_herglotzRieszKernel (c := 0) (R := 1) (z := (z : ℂ)) (by simp) hw)

end TauCeti
end
end
