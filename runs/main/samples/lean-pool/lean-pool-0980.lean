@[expose] public section

noncomputable section

namespace EulerSobolevCoefficientPressure

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerPressureSpatialRegularity
  EulerSpatialSobolevInverse EulerCylinderSobolev EulerCylinderSobolevSpace

open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

theorem pressure_resolvent {q : ℕ} {A B : SmoothCoefficient period}
    (KA : CoefficientJet period standardDirection q A) (KB : CoefficientJet period
        standardDirection q B)
    (κ : ℝ) (m : Vector3) (c d : ℝ) (hc : 0 < c) (hd : 0 < d)
    (hA : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v, v⟫_ℝ)
    (hB : ∀ x v, d * ‖v‖ ^ 2 ≤ ⟪B.coefficient x v, v⟫_ℝ) :
    pressureSobolevOperator period KA κ m c hc hA - pressureSobolevOperator period KB κ m d hd hB =
      (pressureSobolevOperator period KA κ m c hc hA).comp
        ((coefficientSobolevOperator period KB - coefficientSobolevOperator period KA).comp
          (pressureSobolevOperator period KB κ m d hd hB)) := by
  apply ContinuousLinearMap.ext
  intro u
  exact pressure_resolvent_apply period KA KB κ m c d hc hd hA hB u

end EulerSobolevCoefficientPressure
end
end
