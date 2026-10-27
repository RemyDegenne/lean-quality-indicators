@[expose] public section

noncomputable section

open Set Filter Function MeasureTheory

open scoped ContDiff Topology BigOperators

open NavierStokes.OutgoingProfile (Profile)

namespace NavierStokes.ReservedPatches

/-- Radial support right, given by `Real.sqrt (2 * supportRight F XR s)`. -/
noncomputable def radialSupportRight (F : Profile) (XR : ℝ) (s : Slot) : ℝ :=
  Real.sqrt (2 * supportRight F XR s)

end NavierStokes.ReservedPatches
end
end
