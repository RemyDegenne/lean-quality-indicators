public section

open MeasureTheory Set

open scoped ENNReal NNReal Topology

open CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The unit past cylinder including its top time slice. -/
@[expose] def goodPointClosedTopDomain : Set ParabolicPoint :=
  vec3Ball 0 1 ×ˢ Ioc (-1) 0

end ESS
end
end
