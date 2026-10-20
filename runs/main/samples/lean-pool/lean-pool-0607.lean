@[expose] public section

noncomputable section

namespace EulerTransportDerivatives

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerMetricTransport

open scoped ContDiff ENNReal NNReal Topology

section Euclidean

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem directionalDerivative_smooth (a : V) (f : V → W) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (directionalDerivative a f) := by
  exact (hf.fderiv_right (by simp)).clm_apply contDiff_const

end Euclidean
end EulerTransportDerivatives
end
end
