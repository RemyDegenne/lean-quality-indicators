public section

noncomputable section

open scoped EuclideanSpace

namespace TauCeti

open Set

open scoped Manifold ContDiff

open Metric Module

/-- The **unknot** in `S³`: the great circle cut out by the first coordinate plane of `ℝ⁴`, with the
orientation of the standard circle. -/
def unknot : SmoothCircleEmbedding (𝓡 3) (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :=
  SmoothCircleEmbedding.greatCircle complexToEuclideanFour

end TauCeti
end
end
