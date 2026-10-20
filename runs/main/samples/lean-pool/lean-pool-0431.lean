@[expose] public section

noncomputable section

namespace EulerPacketCorrectionCoefficients

open EulerPacketCylinderField EulerAllOrderCorrectionData EulerCorrectionEnergyData
  EulerNonlinearEnergyConstants EulerGevreyGrowthCoefficient EulerGevreyMetricEstimate
   EulerLiftedGradientSpace EulerCylinderSobolevSpace

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (D : EulerTransversePacketProvider.Data U) (P : ℝ) [Fact (0 < P)]
  (Kc : CorrectionCoefficientBudget D P)

theorem growthCoefficient_pos (B0 B1 : ℝ) (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1) :
    0 < growthCoefficient D P Kc B0 B1 := by
  let Z := (Field.zero P D.T).toFieldTower
  let K := sourceMetricBudget D P 0 (by norm_num) Z Z 0
  obtain ⟨h0,h1,hk⟩ := K.constants_nonneg P B0 hB0
  rw [growthCoefficient_eq D P Kc B0 B1 0 (by norm_num) Z Z 0]
  exact energyConstant_pos P _ _ _ _ _ _ _ _ _ _ h0 h1 hk Kc.B_nonneg
    (zero_le_one.trans Kc.M_one_le) hB0 hB1 Kc.A0_nonneg Kc.A2_nonneg K.c_pos

end EulerPacketCorrectionCoefficients
end
end
