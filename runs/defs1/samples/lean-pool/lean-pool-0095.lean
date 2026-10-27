@[expose] public section

namespace NRR

open FoxNeuwirthOrderComplex

namespace FoxNeuwirthOrderComplex

namespace EquivariantPrismStableRelativeBoundary

namespace RouteBFrozenSupportGeometry

open SphereOddDegree

open SphereOddDegree.AffineBarycentricSubdivision

open RefinedAffineMap

open ExplicitAffineRelativeCollar

open ExplicitAffineRelativeCollar.Parameters

open ExplicitAffineRelativeCollar.Polynomials

open ExplicitAffineRelativeCollarCompose

open ExplicitAffineRelativeCollarAssignmentCompose

open ExplicitAffineRelativeCollarReverse

open ExplicitAffineRelativeCollarAssignmentReverse

open ExplicitAffineRelativeCollar.RouteB

open AffinePositiveRayBoundary

open AffinePositiveRayBoundary.VertexMap

open CompatibleRefinedChartHomotopy

open CompatibleChartMapOneStep

open EndpointStackIteratedAffinePullback

variable {p N₀ N₁ M L : Nat}

variable (hp : Nat.Prime p)

/-- Upper one-sided version of frozen positive-support safety. -/
def UpperPositiveSupportRaySafe
    (C : RelativeAffineCellSystem hp N₀ N₁ M L)
    (a : Assignment hp C) : Prop :=
  ∀ (q : C.Cell) (w : StandardSimplex p)
      (i j : Fin (p + 1)), i ≠ j →
    (∀ r : Fin (p - 1),
      deviation hp (affineValue (localVertexMap hp C a q) w) r = 0) →
    0 < mean p (affineValue (localVertexMap hp C a q) w) →
    (∀ k : Fin (p + 1), 0 < w k → (C.vertex q k).time.1 = 1) →
    ¬ (w i = 0 ∧ w j = 0)

end RouteBFrozenSupportGeometry
end EquivariantPrismStableRelativeBoundary
end FoxNeuwirthOrderComplex
end NRR
end
