@[expose] public section

noncomputable section

namespace NavierStokes.ActualSignedPhysicalBinding

open Set Function Filter WeightedClasses CorrectionState TorusMeanRequestRebase

open scoped ContDiff Topology BigOperators

open CorrectionInitialization CorrectionInitialization.ActualPrimary

variable {B N0 : ℕ}

/-- Geometry, given by `ActualSignedGeometry.slotGeometry slots vectors_det (spatialLabel l) 0`. -/
noncomputable def geometry (l : Label B N0) : CommonCoverSolve.Geometry :=
  ActualSignedGeometry.slotGeometry slots vectors_det (spatialLabel l) 0

end NavierStokes.ActualSignedPhysicalBinding
end
end
