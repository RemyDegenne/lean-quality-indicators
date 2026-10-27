@[expose] public section

namespace LeanEval

namespace Topology

namespace ClassificationOfSurfaces

namespace Moise

namespace BrokenLineData

variable {U : Set Plane} (B : BrokenLineData U)

/-- The affine coordinate on edge `i`, shifted to the interval `[i,i+1]`. -/
noncomputable def resolvedEdgeGlobalParameter (i : Fin B.resolvedWalk.length) :
    Plane →ᵃ[ℝ] ℝ :=
  AffineMap.const ℝ Plane (i.val : ℝ) + B.resolvedEdgeParameter i

end BrokenLineData
end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
end
