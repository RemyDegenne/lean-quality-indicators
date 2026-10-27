@[expose] public section

noncomputable section

namespace EulerPacketInductionScales

open Real Filter EulerScale EulerBaseDatum EulerPacketLowConstants
  EulerPacketBaseGuardScales EulerPacketSourceScaleChoice
  EulerPacketSourceScaleSequence EulerPacketSourceScaleActual
  EulerPacketSourceScaleGuards EulerPacketUniformFrequencyScales
  EulerPacketSourceFrequency EulerPacketPressureScale EulerParentRenewalScale
  EulerPacketMovingFrame EulerTransverseActivationSelection EulerMeanHarmonic

open scoped Topology

/-- Pressure increment, given by
`2*gradientConstant*EulerPacketGeometryLowBounds.goodRatio*goodCost J (scaleSequence J X) n
+ initialIncrement J X n`. -/
def pressureIncrement (J : ℕ) (X : ℝ) (n : ℕ) : ℝ :=
  2*gradientConstant*EulerPacketGeometryLowBounds.goodRatio*goodCost J (scaleSequence J X) n +
    initialIncrement J X n

end EulerPacketInductionScales
end
end
