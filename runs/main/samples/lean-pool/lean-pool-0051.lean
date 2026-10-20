@[expose] public section

noncomputable section

namespace NavierStokes.PhysicalGraphBounds

open Set Function

open ProblemStatement

open scoped ContDiff Topology BigOperators

theorem isCompact_annulus (a b : ℝ) : IsCompact (annulus a b) :=
  (isCompact_closedBall 0 b).inter_right (isClosed_le continuous_const continuous_norm)

end NavierStokes.PhysicalGraphBounds
end
end
