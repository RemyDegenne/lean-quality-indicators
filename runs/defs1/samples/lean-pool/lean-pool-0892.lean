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

/-- Agreement: an abbreviation for `A.parent.sourceAgreement A.normal A.normal_unit
A.coordinates A.support A.support_compact A.low`. -/
abbrev agreement : SourceCoefficientAgreement A.meanData A.data :=
  A.parent.sourceAgreement A.normal A.normal_unit A.coordinates A.support A.support_compact A.low

end Input
end EulerPacketInitial
end
end
