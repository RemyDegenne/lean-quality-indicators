section

@[expose] public section

noncomputable section

open Set Filter Function MeasureTheory

open scoped Topology ContDiff BigOperators

namespace NavierStokes.OutgoingPulseBounds

open OutgoingSchedule

/-- Center, given by `c.pulseLength - if j = 0 then 3 else 1`. -/
noncomputable def center (c : Parameters) (j : Fin 2) : ℝ :=
  c.pulseLength - if j = 0 then 3 else 1

end NavierStokes.OutgoingPulseBounds
end
end
end
