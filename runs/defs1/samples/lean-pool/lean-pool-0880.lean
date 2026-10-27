section

@[expose] public section

noncomputable section

namespace EulerStaticEuler

open Set ContinuousLinearMap EulerSmoothLimit EulerLpTranslation
  EulerAllOrderCorrectionData EulerAllOrderDriftCorrection

variable (P : ℝ) [Fact (0 < P)] (u : SmoothL2Field Space) (C R : ℝ)
  (hC : 0 ≤ C) (hR : 0 ≤ R) (hu : u.HasJetBound C R) (hdiv : ∀ x, divergence u.field x = 0)

/-- Local force field, constructed using `SmoothL2Field.mapField`. -/
def localForceField (t : Icc (0 : ℝ) (amplitude P C R hC hR)) : SmoothL2Field Space :=
  SmoothL2Field.mapField (((amplitude P C R hC hR)⁻¹)^2 • ContinuousLinearMap.id ℝ Space)
    ((exactPacket P u C R hC hR hu hdiv).pressure.zeroGraphField
      (EulerTimeRescaling.timeMap (amplitude P C R hC hR) (amplitude_pos P C R hC hR) t))

end EulerStaticEuler
end
end
end
