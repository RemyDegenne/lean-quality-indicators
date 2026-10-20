public section

open Filter Topology ZeroAtInftyContinuousMap

open scoped ZeroAtInfty

variable {I J K L R : Type*} [TopologicalSpace I] [TopologicalSpace J] [DiscreteTopology J]
  [DecidableEq J]

namespace ContinuousLinearMap

open scoped TauCeti.RingOpNorm

section SeminormedRing

variable [SeminormedRing R]

theorem IsRowCompact.neg {u : C₀(J, R) →L[R] C₀(I, R)} (hu : u.IsRowCompact) :
    (-u).IsRowCompact :=
  isRowCompact_of_norm_matrixCoeff_le hu.tendsto_rowNorm fun i j ↦ by
    simpa using hu.norm_matrixCoeff_le_rowNorm i j

end SeminormedRing
end ContinuousLinearMap
end
