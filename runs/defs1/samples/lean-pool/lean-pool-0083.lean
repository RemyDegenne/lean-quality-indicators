@[expose] public section

namespace NRR

open scoped BigOperators

open SphereOddDegree

open SphereOddDegree.AffineBarycentricSubdivision

open FoxNeuwirthOrderComplex

namespace FoxNeuwirthOrderComplex

namespace EquivariantPrismStableRelativeBoundary

namespace RelativeCollarThinSlabsEndpoints

open ExplicitAffineRelativeCollar

open EquivariantPrismGlobalCancellation

open EquivariantPrismNonhorizontalCancellation

open RelativeCollarMiddlePrism

open RelativeCollarMiddlePrismEndpoints

open RelativeCollarMiddlePrismEndpointsCore

open RelativeCollarThinSlabs

open RelativeCollarThinSlabsBoundary

open RefinedAffineMap

variable {p : Nat}

/-- First slab of a positive stack. -/
def firstSlab (m : Nat) (hm : 0 < m) : Fin m :=
  ⟨0, hm⟩

end RelativeCollarThinSlabsEndpoints
end EquivariantPrismStableRelativeBoundary
end FoxNeuwirthOrderComplex
end NRR
end
