@[expose] public section

namespace NRR

open FoxNeuwirthOrderComplex

namespace FoxNeuwirthOrderComplex

namespace EquivariantPrismStableRelativeBoundary

open EquivariantCoordinateHomotopy

open EquivariantPrismGenericPerturbation

open RefinedAffineMap

variable {p : Nat}

/-- A finite generic prism collar whose two horizontal boundaries are prescribed stable
approximations.  The boundary-fixing field includes the necessary equality of endpoint levels with
the horizontal triangulation level `N + L`. -/
structure StableCollar
    (hp : Nat.Prime p)
    {F₀ F₁ : ZeroFreeMap hp}
    (H : ZeroFreeHomotopy hp F₀ F₁)
    (A₀ : StableRegularApproximation hp F₀.map)
    (A₁ : StableRegularApproximation hp F₁.map) where
  /-- The spatial subdivision level of the stable collar. -/
  N : Nat
  /-- The final prism-refinement level of the stable collar. -/
  L : Nat
  /-- The positive norm margin retained by the stable prism perturbation. -/
  m : Real
  positive : 0 < m
  /-- The generic prism perturbation with the prescribed endpoint approximations. -/
  prism : Result hp N L H m
  boundaryFixed : BoundaryFixed hp N L A₀ A₁ prism.assignment

end EquivariantPrismStableRelativeBoundary
end FoxNeuwirthOrderComplex
end NRR
end
