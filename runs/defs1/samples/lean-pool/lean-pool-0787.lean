section

@[expose] public section

namespace NavierStokes.PulseEnergyHistory

noncomputable section

open Set Filter Function MeasureTheory

open scoped Topology ContDiff

open OutgoingSchedule OutgoingTail UniformAngularReset OutgoingHistories

variable {d : TailData} {K : ℝ}

/-- This constant depends only on the fixed parameters `P,m`. -/
noncomputable def historyConstant (P m : ℝ) : ℝ :=
  16 * PulseAmplitude.prefixBoundConstant P m + 13 * (6 * (6 * forceConstant P m) ^ 2 + 2)

end
end NavierStokes.PulseEnergyHistory
end
end
