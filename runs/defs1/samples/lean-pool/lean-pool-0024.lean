@[expose] public section

noncomputable section

open Set Filter Function MeasureTheory

open scoped Topology ContDiff BigOperators

open NavierStokes.OutgoingProfile

namespace NavierStokes.NominalProfile

namespace Controls

variable {F : Profile} {A : AxisStage F} (c : Controls A)

/-- Normalized E, given by `joinedE F A.normalization c.shapeTime c.initialShape c.seedF
c.seedU`. -/
noncomputable def normalizedE : Field :=
  joinedE F A.normalization c.shapeTime c.initialShape c.seedF c.seedU

end Controls
end NavierStokes.NominalProfile
end
end
