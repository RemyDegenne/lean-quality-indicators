@[expose] public section

noncomputable section

namespace NavierStokes.DirectAngularDiagonal

open Set Function Filter ProblemStatement

open scoped Topology ContDiff BigOperators

theorem physicalDomain_open {U : Set Slow} (hU : IsOpen U) : IsOpen (physicalDomain U) :=
  hU.preimage slowPoint_smooth.continuous

end NavierStokes.DirectAngularDiagonal
end
end
