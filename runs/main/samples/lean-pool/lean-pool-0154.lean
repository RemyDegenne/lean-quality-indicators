section

section

@[expose] public section

noncomputable section

namespace EulerStaticEuler

open Set ContinuousLinearMap EulerSmoothLimit EulerLpTranslation
  EulerLiftedGradientSpace EulerAllOrderCorrectionData EulerAllOrderDriftCorrection
  EulerPacketCylinderField EulerCorrectionAssembly EulerMetricTransport
  EulerCanonicalGraphPotential EulerGraphPressurePotential

variable (P : ℝ) [Fact (0 < P)] (u : SmoothL2Field Space) (C R : ℝ)
  (hC : 0 ≤ C) (hR : 0 ≤ R) (hu : u.HasJetBound C R) (hdiv : ∀ x, divergence u.field x = 0)
  (hodd : ∀ x, u.field (-x) = -u.field x)

include hodd

theorem unit_force_odd (t : ℝ) (x : Space) :
    EulerConstantEuler.force (exactPacket P u C R hC hR hu hdiv) (t,-x) =
      -EulerConstantEuler.force (exactPacket P u C R hC hR hu hdiv) (t,x) := by
  change (exactPacket P u C R hC hR hu hdiv).pressure.pointField
      (projIcc 0 1 zero_le_one t) (-x,0) =
    -(exactPacket P u C R hC hR hu hdiv).pressure.pointField (projIcc 0 1 zero_le_one t) (x,0)
  rw [unit_pressure_point,unit_pressure_point]
  have h := (correctionBudget P u C R hC hR hu hdiv).pointPressure_odd P
    (symmetry P u C R hC hR hodd) (projIcc 0 1 zero_le_one t) (x,0)
  simpa only [Prod.neg_mk,neg_zero] using h

end EulerStaticEuler
end
end
end
end
