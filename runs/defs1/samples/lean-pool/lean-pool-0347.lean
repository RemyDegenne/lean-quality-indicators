@[expose] public section

namespace NRR

open scoped BigOperators

open SphereOddDegree

open SphereOddDegree.AffineBarycentricSubdivision

open FoxNeuwirthOrderComplex

namespace FoxNeuwirthOrderComplex

namespace EquivariantPrismHorizontalEndpointIdentification

open AffinePositiveRayBoundary

open EquivariantPrismVertexParameters

open EquivariantPrismGenericityPolynomials

open EquivariantPrismGenericPerturbation

open EquivariantPrismGlobalCancellation

open EquivariantPrismNonhorizontalCancellation

open SubdivisionPrismCharts

open RefinedAffineMap

variable {p : Nat}

/-- The upper endpoint pairing of an arbitrary facet-map weight. -/
noncomputable def weightedUpperEndpointPairing
    (hp : Nat.Prime p) (N L : Nat)
    (W : (Delta (p - 1) → Realization p × Set.Icc (0 : Real) 1) → ZMod p) : ZMod p :=
  ∑ q : TopCell hp N,
    ((PrimeOrbitCycle.orbitCycle hp).coefficient q.1 * subdivisionSign N q.2) *
      ∑ eta : Fin L → Equiv.Perm (Fin p),
        subdivisionSign L eta *
          W (upperEndpointMap (endpointSpatialMap hp N L q eta))

end EquivariantPrismHorizontalEndpointIdentification
end FoxNeuwirthOrderComplex
end NRR
end
