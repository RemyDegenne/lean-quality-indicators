section

@[expose] public section

noncomputable section

open Set Filter MeasureTheory

open scoped Topology ContDiff

open NavierStokes.OutgoingSchedule NavierStokes.OutgoingTail

open NavierStokes.AngularMomentReset NavierStokes.UniformAngularReset

open NavierStokes.FuturePressureBounds

namespace NavierStokes.CorrectedPressureBounds

theorem pressureChange_joint_contDiff {d : TailData} {K : ℝ} (w : ResetWitness d K) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => pressureChange w p.1 p.2) := by
  have heq : (fun p : ℝ × ℝ => pressureChange w p.1 p.2) = fun p : ℝ × ℝ =>
      (1 / 2) * ∫ t in (d.releaseStart - 4)..p.1, editDensity w (t, p.2) := by
    funext p
    exact pressureChange_eq_partial w p.1 p.2
  rw [heq]
  exact contDiff_const.mul (intervalPrimitive_contDiff (editDensity_contDiff w) _)

end NavierStokes.CorrectedPressureBounds
end
end
end
