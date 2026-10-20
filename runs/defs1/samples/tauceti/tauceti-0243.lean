public section

open AlgebraicGeometry CategoryTheory

namespace TauCeti.GeneralLinear

universe u v

variable (R : Type u) [CommRing R] {N : ℕ}

/-- The coordinate Hopf algebra of the weight parabolic attached to `w`. -/
noncomputable abbrev weightParabolicCoordinateHopfAlgebra (w : Fin N → ℤ) :
    _root_.CommHopfAlgCat.{u} R :=
  CommHopfAlgCat.quotient (coordinateHopfAlgebra R N)
    (weightParabolicDefiningHopfIdeal R w)

end TauCeti.GeneralLinear
end
