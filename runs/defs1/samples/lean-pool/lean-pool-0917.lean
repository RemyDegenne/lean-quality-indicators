@[expose] public section

noncomputable section

namespace NavierStokes.GaugeMassPreservation

open Set Filter Function MeasureTheory

open scoped ContDiff Topology Interval BigOperators

open VariableGaugeMean LocalSignedRequest CorrectionState

/-- Point: an abbreviation for `PressureStream.Lift Plane`. -/
abbrev Point := PressureStream.Lift Plane

end NavierStokes.GaugeMassPreservation
end
end
