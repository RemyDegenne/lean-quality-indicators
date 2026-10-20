section

@[expose] public section

noncomputable section

namespace EulerPhysicalGraphFlowBounds.Data

open Set EulerLiftedGradientSpace EulerSmoothBanachFlow EulerSmoothFlowGevrey
  EulerGraphInvariantFlow EulerVolterraConvolution

variable {P T : ℝ} [Fact (0 < P)] (G : EulerPhysicalGraphFlowBounds.Data P T)

theorem physicalVelocityCoefficient_time (k : ℝ) (m : Vector3) (ell : ℝ) :
    SmoothTimeField.TimeDerivative T G.time_nonneg
      (G.physicalVelocityCoefficient k m ell) (G.physicalAccelerationCoefficient k m ell) :=
  physicalCoefficient_timeDerivative k m T G.time_nonneg
    G.coverVelocityCoefficient G.coverAccelerationCoefficient ell G.coverVelocityCoefficient_time

end EulerPhysicalGraphFlowBounds.Data
end
end
end
