@[expose] public section

noncomputable section

namespace EulerAllOrderDriftCorrection

open Set Finset EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerAllOrderCorrectionData EulerCorrectionEnergyData EulerCorrectionEnergyMajorants
  EulerGevreyMetricEstimate EulerGevreyRadiusReduction EulerSobolevGevreyOperators

variable (period : ℝ) [Fact (0 < period)]

variable {T : ℝ} {hT : 0 < T} {A : Data period T}

theorem Budget.fieldTower_weightedNorm_delta (B : Budget period hT A)
    (s N : ℕ) (hN : N + 6 ≤ s) (t : Icc (0 : ℝ) T) :
    weightedNorm period 6 N (B.radius t) ((B.fieldTower period).realization s t) ≤
      B.correctionSize period := by
  have hv : value period ((B.fieldTower period).realization s t) =
      value period (B.solution period (N+6) (by omega) t) := by
    rw [(B.fieldTower period).value_eq]
    exact (B.solution_value_common period (N+6) (by omega) t).symm
  rw [weightedNorm_unique period 6 N (B.radius t) _ _ hv hN (by omega)]
  have h := weightedNorm_le_energy period N (by omega : N+6 ≤ (N+6)+1) (B.radius t)
    ((B.spatial (N+6) (by omega)).full.radius_pos t) (B.metric.operatorPath period t)
    (B.solution period (N+6) (by omega) t) B.metric.c B.metric.c_pos
    (B.metric.operator_coercive period t)
  exact h.trans (mul_le_mul_of_nonneg_left
    (B.solution_energy period (N+6) (by omega) N (by omega) (by omega) t).2
    (zero_le_one.trans (metricAmplification_one_le B.metric.c_pos)))

end EulerAllOrderDriftCorrection
end
end
