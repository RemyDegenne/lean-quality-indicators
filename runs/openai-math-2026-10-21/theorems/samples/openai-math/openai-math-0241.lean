namespace OAI

noncomputable section

open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise Distributions

open Set Filter

namespace SmoothLocal.Pulse

open SmoothLocal.Geometry SmoothLocal.Perturbation

theorem pulseScaleBound_pos (q0 delta : ℝ) : 0 < pulseScaleBound q0 delta := by
  unfold pulseScaleBound
  positivity

end SmoothLocal.Pulse
end
end OAI
