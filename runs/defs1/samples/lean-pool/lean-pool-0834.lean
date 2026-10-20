@[expose] public section

namespace NRR

open scoped BigOperators

open SphereOddDegree

open SphereOddDegree.AffineBarycentricSubdivision

open FoxNeuwirthOrderComplex

namespace FoxNeuwirthOrderComplex

namespace EquivariantPrismStableRelativeBoundary

namespace RelativeCollarThinSlabsBoundary

open ExplicitAffineRelativeCollar

open EquivariantPrismGlobalCancellation

open EquivariantPrismNonhorizontalCancellation

open EquivariantPrismHorizontalEndpointIdentification

open RelativeCollarMiddlePrism

open RelativeCollarMiddlePrismBoundary

open RelativeCollarMiddlePrismEndpoints

open RelativeCollarThinSlabs

open RefinedAffineMap

open EquivariantPrismVertexParameters

variable {p : Nat}

/-- Embed one base-prism facet occurrence into slab `r`. -/
def stackOccurrence
    (hp : Nat.Prime p) (N m : Nat) (hm : 0 < m)
    (r : Fin m) (o : (BaseCells hp N).FacetOccurrence) :
    (StackCells hp N m hm).FacetOccurrence :=
  ((r, o.1), o.2)

end RelativeCollarThinSlabsBoundary
end EquivariantPrismStableRelativeBoundary
end FoxNeuwirthOrderComplex
end NRR
end
