@[expose] public section

noncomputable section

open Set Function Filter MeasureTheory

open scoped Topology ContDiff

open NavierStokes.OutgoingSchedule NavierStokes.OutgoingTail

open NavierStokes.AngularMomentReset NavierStokes.UniformAngularReset

namespace NavierStokes.ReleaseMoments

/-- Power weight, given by `powerConstant d * Real.exp ((1 - d.h) * y)`. -/
noncomputable def powerWeight (d : TailData) (y : ℝ) : ℝ :=
  powerConstant d * Real.exp ((1 - d.h) * y)

end NavierStokes.ReleaseMoments
end
end
