public section

noncomputable section

open scoped ENNReal Topology

namespace TauCeti

variable (𝕜 E F : Type*) [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- An operator gauge on `E →L[𝕜] F`: an extended nonnegative function on bounded operators that
is subadditive, absolutely homogeneous and dominates the operator norm. -/
structure OperatorGauge where
  /-- The gauge of a bounded operator. -/
  toFun : (E →L[𝕜] F) → ℝ≥0∞
  /-- The gauge is subadditive. -/
  map_add_le' (A B : E →L[𝕜] F) : toFun (A + B) ≤ toFun A + toFun B
  /-- The gauge is absolutely homogeneous. -/
  map_smul' (c : 𝕜) (A : E →L[𝕜] F) : toFun (c • A) = ‖c‖ₑ * toFun A
  /-- The gauge dominates the extended operator norm. -/
  enorm_le' (A : E →L[𝕜] F) : ‖A‖ₑ ≤ toFun A

end TauCeti
end
end
