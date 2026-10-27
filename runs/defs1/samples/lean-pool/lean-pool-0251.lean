section

section

section

@[expose] public section

noncomputable section

namespace EulerStaticEuler

open Set EulerSmoothLimit EulerLiftedGradientSpace EulerLpTranslation
  EulerAllOrderDriftCorrection EulerAllOrderCorrectionData EulerSobolevGevreyOperators
  EulerGevreyCorrectionSourceBounds EulerGevreyMetricEstimate EulerConstantCorrection

variable (P : ℝ) [Fact (0 < P)]

/-- Static source cost, given by `sourceBound P 1 1 0 0 1 baseErrorFactor
((8/EulerSmallCorrection.initialRadius (mixedRadius R))*baseErrorFactor)`. -/
def staticSourceCost (R : ℝ) : ℝ :=
  sourceBound P 1 1 0 0 1 baseErrorFactor
    ((8/EulerSmallCorrection.initialRadius (mixedRadius R))*baseErrorFactor)

end EulerStaticEuler
end
end
end
end
end
