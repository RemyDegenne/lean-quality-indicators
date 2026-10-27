@[expose] public section

namespace NRR

open FoxNeuwirthOrderComplex

open MeasureTheory

open scoped BigOperators

namespace FoxNeuwirthOrderComplex

namespace EquivariantPrismStableRelativeBoundary

namespace ExplicitAffineRelativeCollar

namespace RouteB

open AffinePositiveRayBoundary

open AffinePositiveRayBoundary.VertexMap

open Parameters

open Polynomials

open RelativeGenericity

variable {p N₀ N₁ M L : Nat}

variable (hp : Nat.Prime p)

variable (C : RelativeAffineCellSystem hp N₀ N₁ M L)

/-- Joint deviation coordinate. -/
noncomputable def jointDeviation
    (base : Assignment hp C) (κ : MixedFaceCase hp C)
    (z : MovableParameterSpace hp C × StandardSimplex p)
    (r : Fin (p - 1)) : Real :=
  deviation hp (fun j => jointAffineCoordinate hp C base κ z j) r

end RouteB
end ExplicitAffineRelativeCollar
end EquivariantPrismStableRelativeBoundary
end FoxNeuwirthOrderComplex
end NRR
end
