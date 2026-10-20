public section

open AlgebraicGeometry CategoryTheory WithConv

namespace TauCeti.GeneralLinear.Dynamic

universe u v

variable (R : Type u) [CommRing R] {N : ℕ}

/-- The relative quotient spectrum cut out inside the weight parabolic is canonically
isomorphic to the weight-unipotent group scheme. -/
noncomputable def weightUnipotentInParabolicGroupSchemeIso (w : Fin N → ℤ) :
    CommHopfAlgCat.quotientSpec (weightParabolicCoordinateHopfAlgebra R w)
        (weightUnipotentInParabolicHopfIdeal R w) ≅
      weightUnipotentGroupScheme R w :=
  (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).mapIso
    (weightUnipotentInParabolicCoordinateIso R w).op

end TauCeti.GeneralLinear.Dynamic
end
