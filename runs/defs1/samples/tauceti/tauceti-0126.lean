public section

universe v

namespace TauCeti.TypeBSpinCarrier

open AlgebraicGeometry CategoryTheory

open TauCeti.UniversalEnvelopingAlgebra

open scoped CategoryTheory.MonObj

attribute [local instance 100] LieRing.ofAssociativeRing

attribute [local instance high] Algebra.toModule

variable (n : ℕ)

/-- The coordinate basis of the first isotropic summand. -/
noncomputable abbrev polarizationBasis := TauCeti.splitOddBasis ℚ (n + 1)

end TauCeti.TypeBSpinCarrier
end
