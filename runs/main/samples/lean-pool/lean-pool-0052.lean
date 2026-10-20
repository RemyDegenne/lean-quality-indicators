@[expose] public section

noncomputable section

namespace EulerSobolevDriftNorm

open MeasureTheory Filter EulerSobolev EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerCylinderSobolev EulerSpatialSobolevInverse EulerMetricTransport EulerH6Pressure
  EulerH6Nonlinear EulerJetProductBounds EulerSobolevGevreyOperators
  EulerFunctionalVelocity EulerStrongSmoothJet EulerVectorCylinder EulerRealCylinder

open scoped ContDiff ENNReal Topology

variable (period : ℝ) [Fact (0 < period)]

omit [Fact (0 < period)] in
theorem velocityMap_norm_le_four (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1) :
    ‖velocityMap L‖ ≤ 4 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro z
  calc
    ‖velocityMap L z‖ ≤ ∑ i : Fin 4, ‖velocityMap L z i‖ :=
        EulerSobolevDerivativeNorm.norm_le_sum_coordinates 4 _
    _ ≤ ∑ _i : Fin 4, ‖z‖ := Finset.sum_le_sum fun i _ =>
      ((L i).le_opNorm z).trans (by simpa using mul_le_mul_of_nonneg_right (hL i) (norm_nonneg z))
    _ = _ := by simp

end EulerSobolevDriftNorm
end
end
