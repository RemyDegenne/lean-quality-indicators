@[expose] public section

namespace NRR

namespace FoxNeuwirthOrderComplex

namespace EquivariantPrismStableRelativeBoundary

namespace RelativeSubdivisionOneStepCells

open scoped BigOperators

open SphereOddDegree

open SphereOddDegree.AffineBarycentricSubdivision

open RefinedAffineMap

open ExplicitAffineRelativeCollar

open EquivariantPrismGenericityNonzero

open EquivariantPrismVertexParameters

open SubdivisionPrismAffine

variable {p : Nat}

/-- One coordinate of a refined realization chart as a linear functional of its standard-simplex
barycentric coordinate vector. -/
noncomputable def refinedCoordinateLinear
    (hp : Nat.Prime p) (N : Nat) (q : TopCell hp N) (c : BarredPermutation p) :
    (Fin (p - 1 + 1) → Real) →ₗ[Real] Real :=
  (realizationCoordinateLinear (ReferenceAffineOrbitCount.topRepr hp q.1) c).comp
    (affineCompLinear (p - 1) N
      (fun k => Simplex.refinementIndexPerm (q.2 k)))

end RelativeSubdivisionOneStepCells
end EquivariantPrismStableRelativeBoundary
end FoxNeuwirthOrderComplex
end NRR
end
