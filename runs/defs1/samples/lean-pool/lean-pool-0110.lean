@[expose] public section

namespace NavierStokes.ActualInitialCoherence

noncomputable section

open Set Function Filter

open scoped ContDiff Topology BigOperators

open CorrectionState MeanIncrementBounds MeanStateRegularity PhysicalResidualNaturality

/-- Plane: an abbreviation for `PressureStream.Plane`. -/
abbrev Plane := PressureStream.Plane

end
end NavierStokes.ActualInitialCoherence
end
