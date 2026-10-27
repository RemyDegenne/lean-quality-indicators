@[expose] public section

namespace NRR

open CategoryTheory AlgebraicTopology Simplicial SimplexCategory Limits

open FoxNeuwirthOrderComplex

open SphereOddDegree

open SphereOddDegree.AffineBarycentricSubdivision

namespace FoxNeuwirthOrderComplex

namespace EquivariantPrismStableRelativeBoundary

namespace RelativeSubdivisionCellParameters

open EquivariantCoordinateHomotopy

open RefinedAffineMap

open EquivariantPrismVertexParameters

open StableCollarRelativeSubdivision

variable {p : Nat}

section RelativeCylinderParameters

variable (p : Nat) {n : Nat}

variable (B : RelativeSubdivisionBoundary (ZMod p) (RelativeCylinder p) n)

/-- Parameter orbits represented only by movable interior or spatial-side vertices. -/
abbrev MovableParameter := {q : Parameter p B // ¬ IsFrozenParameter p B q}

end RelativeCylinderParameters
end RelativeSubdivisionCellParameters
end EquivariantPrismStableRelativeBoundary
end FoxNeuwirthOrderComplex
end NRR
end
