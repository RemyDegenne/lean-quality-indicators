@[expose] public section

noncomputable section

namespace EulerGevreyCorrectionBound

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerCylinderSobolevSpace
    EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerH6Pressure EulerSobolevGevreyOperators
      EulerGevreyCorrectionForcing
  EulerBasePressureCommutator EulerBaseTransportL2 EulerH6Nonlinear EulerSobolevTransportCommutator
  EulerGevreyPressureTransport EulerSobolevCoefficientPressure EulerGevreyUniformConstants
  EulerGevreyMetricComparison EulerWeightedCylinderEnergy

variable (period : ℝ) [Fact (0 < period)]

theorem lossConstant_nonneg {M : ℝ} (hM : 0 ≤ M) : 0 ≤ lossConstant period M :=
  mul_nonneg (by linarith only [hM]) (productConstant_nonneg period 3)

end EulerGevreyCorrectionBound
end
end
