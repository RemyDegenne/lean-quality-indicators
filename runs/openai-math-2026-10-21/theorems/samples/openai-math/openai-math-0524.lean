namespace OAI

open scoped BigOperators Topology NNReal ENNReal

open MeasureTheory ProbabilityTheory Filter Real

noncomputable section

namespace SquareRootDegree

namespace Amplification

open Observations Switching GaussianGain MomentTransfer

attribute [local instance] Classical.propDecidable

attribute [instance] Observation.coordFintype Observation.coordDecidableEq Observation.labelFintype

theorem costFactor_pos : 0 < costFactor := by
  unfold costFactor
  omega

end Amplification
end SquareRootDegree
end
end OAI
