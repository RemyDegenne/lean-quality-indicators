namespace OAI

section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set

open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter

open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace

open scoped Pointwise

namespace SphericalPerceptron

open Matrix

open scoped RealInnerProductSpace MatrixOrder

open TopologicalSpace

open scoped Polynomial

open scoped ContDiff

lemma heatTilt_abs_le (s d : ℝ≥0) (f h : ℝ →ᵇ ℝ) (x : ℝ) :
    |heatTilt s d f h x| ≤ ‖h‖ := by
  rw [abs_le]
  constructor
  · have hh := heatTilt_mono s d f (BoundedContinuousFunction.const ℝ (-‖h‖)) h
      (fun y => (abs_le.mp (h.norm_coe_le_norm y)).1) x
    simpa only [heatTilt_const] using hh
  · have hh := heatTilt_mono s d f h (BoundedContinuousFunction.const ℝ ‖h‖)
      (fun y => (abs_le.mp (h.norm_coe_le_norm y)).2) x
    simpa only [heatTilt_const] using hh

end SphericalPerceptron
end
end
end
end OAI
