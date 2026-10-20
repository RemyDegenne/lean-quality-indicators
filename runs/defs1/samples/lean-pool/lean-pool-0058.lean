@[expose] public section

noncomputable section

namespace NavierStokes.ActualPeriodizedSignedRealization

open Set Function Filter

open HarmonicCalculus LinearWaveBounds WeightedClasses

open ProblemStatement

open scoped Topology ContDiff BigOperators InnerProductSpace

/-- Plane: an abbreviation for `TorusInverse.Plane`. -/
abbrev Plane := TorusInverse.Plane

end NavierStokes.ActualPeriodizedSignedRealization
end
end
