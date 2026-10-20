section

@[expose] public section

noncomputable section

open Set Filter Function MeasureTheory

open scoped ContDiff Topology

open NavierStokes.OutgoingProfile NavierStokes.OutgoingTail

namespace NavierStokes.OutgoingDilation

theorem patchClock_after_hold (F : Profile) : F.data.core.holdStart < patchClock F := by
  dsimp only [patchClock, OutgoingSchedule.Parameters.pulseStart]
  linarith [F.data.core.wait_gt]

end NavierStokes.OutgoingDilation
end
end
end
