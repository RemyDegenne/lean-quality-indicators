@[expose] public section

namespace NavierStokes.CommonCoverClass

noncomputable section

open Set Function

open scoped ContDiff BigOperators Topology

open TorusInverse

/-- CCS: an abbreviation for `CommonCoverSolve.Geometry`. -/
abbrev CCS := CommonCoverSolve.Geometry

end
end NavierStokes.CommonCoverClass
end
