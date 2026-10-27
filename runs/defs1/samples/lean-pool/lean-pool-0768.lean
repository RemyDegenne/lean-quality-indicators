@[expose] public section

noncomputable section

namespace EulerAllOrderDriftCorrection

open Set MeasureTheory EulerAllOrderCorrectionData EulerLiftedGradientSpace EulerSmoothLimit
  EulerPacketCylinderField EulerPacketProfileRecursion EulerCylinderSmoothOrbit
  EulerLiftedSmoothTimeField EulerLiftedTransportTrace EulerMetricTransport

open scoped ContDiff BoundedContinuousFunction

variable (P : ℝ) [Fact (0 < P)] {T : ℝ} {hT : 0 < T} {A : Data P T}
  (B : Budget P hT A) {raw raw_t : VectorField}

/-- Packet coefficient, given by `G.toSmoothTimeField.add (B.correctionCoefficient P)`. -/
def Budget.packetCoefficient (G : Field P T raw) :
    SmoothTimeField (Icc (0 : ℝ) T) LiftTangent Space :=
  G.toSmoothTimeField.add (B.correctionCoefficient P)

end EulerAllOrderDriftCorrection
end
end
