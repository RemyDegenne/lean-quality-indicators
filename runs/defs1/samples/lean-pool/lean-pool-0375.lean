@[expose] public section

namespace NRR

open SphereOddDegree

open SphereOddDegree.AffineBarycentricSubdivision

open FoxNeuwirthOrderComplex

namespace FoxNeuwirthOrderComplex

namespace EquivariantPrismStableRelativeBoundary

namespace EndpointFaceRefinement

open EquivariantPrismNonhorizontalCancellation

open EquivariantPrismHorizontalEndpointIdentification

open RefinedAffineMap

open SubdivisionPrismCharts

variable {p : Nat}

attribute [local simp] ContinuousMap.comp_apply

/-- Reindex a horizontal endpoint simplex as a top cell at the combined refinement level. -/
noncomputable def endpointTopCell
    (hp : Nat.Prime p) (N L : Nat)
    (q : TopCell hp N) (eta : RefinementWord p L) :
    TopCell hp (N + L) :=
  (q.1, appendRefinementWord N L q.2 eta)

end EndpointFaceRefinement
end EquivariantPrismStableRelativeBoundary
end FoxNeuwirthOrderComplex
end NRR
end
