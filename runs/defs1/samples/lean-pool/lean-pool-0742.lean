@[expose] public section

namespace NRR

namespace FoxNeuwirthOrderComplex

namespace EquivariantPrismStableRelativeBoundary

namespace CompatibleChartMapOneStep

open scoped BigOperators

open SphereOddDegree

open SphereOddDegree.AffineBarycentricSubdivision

open RefinedAffineMap

open ExplicitAffineRelativeCollar

open ExplicitAffineRelativeCollar.Parameters

open AffinePositiveRayBoundary

open CompatibleRefinedChartHomotopy

open ExplicitAffineRelativeCollarAssignmentCompose

open ExplicitAffineRelativeCollar.Polynomials

open AffinePositiveRayBoundary.VertexMap

open EndpointFaceRefinement

variable {p : Nat}

/-- Canonical one-step assignment associated with a compatible chart map. -/
noncomputable def assignment
    (hp : Nat.Prime p) {N : Nat} (K : ChartMap hp N) :
    Assignment hp (Cells hp N) :=
  assignmentOfEquivariantVector (Cells hp N) (globalVector hp K)
    (globalVector_smul hp K)

end CompatibleChartMapOneStep
end EquivariantPrismStableRelativeBoundary
end FoxNeuwirthOrderComplex
end NRR
end
