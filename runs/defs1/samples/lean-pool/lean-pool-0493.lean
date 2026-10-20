@[expose] public section

noncomputable section

open Set Filter Function MeasureTheory

open scoped Topology ContDiff BigOperators

namespace NavierStokes.OutgoingSchedule

/-- Prefix coefficient, given by `(if i = 0 then prefixM c else prefixJ c) / momentScale c i`. -/
def prefixCoefficient (c : Parameters) (i : Fin 2) : ℝ :=
  (if i = 0 then prefixM c else prefixJ c) / momentScale c i

end NavierStokes.OutgoingSchedule
end
end
