section

@[expose] public section

namespace NavierStokes.TrueConeLoop

noncomputable section

open Set Filter MeasureTheory

open SmoothLoop LoopMoments LoopVariance ConeAlgebra

open scoped ContDiff Topology Interval

theorem correctionRoot_contDiff (δ : ℝ) (hδ : 0 < δ) : ContDiff ℝ ∞ (correctionRoot δ) := by
  apply contDiff_iff_contDiffAt.mpr
  intro v
  by_cases hv : v < targetSpeed δ
  · exact (speedCutoff_contDiff δ).contDiffAt.mul
      ((contDiffAt_const.sub contDiffAt_id).sqrt (ne_of_gt (sub_pos.mpr hv)))
  · have hhigh : highSpeed δ < v := by
      dsimp [highSpeed, targetSpeed] at *
      linarith only [hδ, hv]
    apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ => (0 : ℝ)) v).congr_of_eventuallyEq
    filter_upwards [lt_mem_nhds hhigh] with w hw
    exact correctionRoot_zero δ w hδ hw.le

end
end NavierStokes.TrueConeLoop
end
end
