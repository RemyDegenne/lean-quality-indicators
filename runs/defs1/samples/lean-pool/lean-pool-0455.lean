@[expose] public section

noncomputable section

namespace EulerPacketInitial

open Set EulerSmoothLimit EulerSpatialCutoffs EulerParentPacketFrames
  EulerTransversePacketProvider EulerPacketSourceGeometry EulerPacketCylinderField
  EulerPacketTerminalDatum EulerPacketUniformSource EulerPhysicalL2Scaling
  EulerPacketSourceFrequency EulerLpTranslation EulerAllOrderDriftCorrection

namespace Input

variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (A : Input U)

/-- Mean, constructed using `initializedInitialMean`. -/
def mean (k : ℝ) : Space → Space :=
  initializedInitialMean A.meanData A.data A.historyTime A.history_pos A.history_lt A.history
    A.geometry.δ A.delta_pos A.terminal A.cutoff_support A.alpha (truncation k) k

end Input
end EulerPacketInitial
end
end
