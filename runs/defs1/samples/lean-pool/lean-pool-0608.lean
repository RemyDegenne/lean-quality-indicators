@[expose] public section

attribute [local instance] FiniteDimensional.hasContDiffBump

noncomputable section

namespace EulerCylinderMollifier

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerCylinderCoordinates
  EulerSobolev EulerNoncompactTransport EulerSpatialSobolevInverse

open scoped ContDiff ENNReal NNReal Topology Convolution

variable (period : ℝ) [Fact (0 < period)]

/-- The bounded L² approximate-identity operator, with operator norm at most one. -/
def mollifierOperator (n : ℕ) : LiftL2 period →L[ℝ] LiftL2 period :=
  (mollifierLinearMap period n).mkContinuous 1 (fun f => by
    change ‖mollify period n f‖ ≤ 1 * ‖f‖
    simpa only [one_mul] using mollify_norm_le period n f)

end EulerCylinderMollifier
end
end
