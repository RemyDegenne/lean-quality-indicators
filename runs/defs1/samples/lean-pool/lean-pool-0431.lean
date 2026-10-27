@[expose] public section

noncomputable section

namespace EulerH6Nonlinear

open MeasureTheory EulerSobolev EulerCylinderSobolev EulerCylinderAlgebra
  EulerLiftedGradientSpace EulerMetricTransport EulerTransportDerivatives EulerVectorCylinder
  EulerJetProductBounds EulerSpatialSobolevInverse EulerPacketWeights

open scoped ContDiff ENNReal Topology

variable (period : ℝ) [Fact (0 < period)]

/-- Actual transport in the four cylinder coordinates; angle is the first coordinate. -/
def transportField (q : ℕ) (b : LiftDomain period → Domain 4) (e : LiftDomain period → Domain q) :
    LiftDomain period → Domain q :=
  ∑ i : Fin 4, (fun x => b x i • fieldDerivative period (standardDirection i) e x)

end EulerH6Nonlinear
end
end
