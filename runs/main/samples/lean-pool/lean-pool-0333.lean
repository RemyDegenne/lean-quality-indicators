@[expose] public section

attribute [local instance] FiniteDimensional.hasContDiffBump

noncomputable section

namespace EulerCylinderMollifier

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerCylinderCoordinates
  EulerSobolev EulerNoncompactTransport EulerSpatialSobolevInverse

open scoped ContDiff ENNReal NNReal Topology Convolution

variable (period : ℝ) [Fact (0 < period)]

theorem mollifierKernel_integral (n : ℕ) : ∫ x, mollifierKernel n x = 1 :=
  (mollifierBump n).integral_normed

end EulerCylinderMollifier
end
end
