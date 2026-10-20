@[expose] public section

namespace NRR

open scoped BigOperators

open SphereOddDegree

open SphereOddDegree.AffineBarycentricSubdivision

open FoxNeuwirthOrderComplex

namespace FoxNeuwirthOrderComplex

namespace EquivariantPrismStableRelativeBoundary

namespace RelativeCollarMiddlePrismBoundary

open ExplicitAffineRelativeCollar

open RelativeCollarMiddlePrism

open EquivariantPrismVertexParameters

open EquivariantPrismGlobalCancellation

open EquivariantPrismNonhorizontalCancellation

open EquivariantPrismHorizontalEndpointIdentification

open SubdivisionPrismCharts

open RefinedAffineMap

variable {p : Nat}

/-- Upper boundary coefficient of one middle-prism facet orbit. -/
noncomputable def upperBoundaryCoefficient
    (hp : Nat.Prime p) (N L : Nat)
    (s : (Cells hp N L).Facet) : ZMod p :=
  upperEndpointPairing hp N L (facetOrbitIndicator hp N L s)

end RelativeCollarMiddlePrismBoundary
end EquivariantPrismStableRelativeBoundary
end FoxNeuwirthOrderComplex
end NRR
end
