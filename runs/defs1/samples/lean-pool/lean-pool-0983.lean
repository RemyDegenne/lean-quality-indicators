@[expose] public section

open Filter MeasureTheory Set

open scoped ENNReal BigOperators Function Topology

namespace QuadraticCarleson

namespace CalderonZygmundDyadicStopping

noncomputable
section

/-- The subtype of intrinsic stopping nodes for the data-dependent root
length. It is countable because the dyadic forest itself is encodable. -/
def stoppingNode (f : ℝ → ℂ) :=
  {p : DyadicNode // IsStoppingNode f (rootLength f) p}

end
end CalderonZygmundDyadicStopping
end QuadraticCarleson
end
