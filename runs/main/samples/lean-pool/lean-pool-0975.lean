@[expose] public section

noncomputable section

open Set Filter Function MeasureTheory

open scoped Topology ContDiff BigOperators

open NavierStokes.OutgoingProfile

namespace NavierStokes.NominalProfile

namespace Controls

variable {F : Profile} {A : AxisStage F} (c : Controls A)

theorem reference_before_big : 0 < c.reference.bigTime :=
  c.referenceWidth_pos.trans_le c.before_big

end Controls
end NavierStokes.NominalProfile
end
end
